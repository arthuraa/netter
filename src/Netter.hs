{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}

{-|

This module defines a simple imperative programming language.  Programs can
manipulate scalar variables and sample values from a probability distribution.
Loops, recursion and arrays are missing, but can be emulated to some extent.  A
typical program looks like this:

@
prog :: Prog ()
prog = ...

-- Compile the program to a Prism model and print the output.
main :: IO ()
main = compile prog
@

-}

module Netter (
  -- * Expressions and commands
  --
  -- | The language has a fairly standard separation between expressions
  -- ('Expr') and commands ('Prog').  Expressions map almost directly to
  -- expressions in the Prism model checker, and include arithmetic on integers
  -- and floating-point numbers, as well as logical operations.  Expressions are
  -- not typed, and might lead to ill-formed output code; e.g. if you try to add
  -- an integer to a boolean.
  --
  -- Commands include assignments, sampling and conditionals.  To avoid clashes
  -- with common Haskell names, most infix operators are prefixed with @.@
  -- (e.g. '.+'), and function names are primed (e.g. 'max'').  'Prog' has the
  -- structure of a monad.  The type @Prog a@ is builds a partial Prism program
  -- and returns a value of type 'a'.  When 'a' is '()', we can roughly view
  -- this as a command.

    Expr
  , Prog
  -- * Variables and rewards
  , namedVar
  , var
  , rewards
  -- * Expressions
  , int
  , double
  , (.<-), (.<-$), unif
  , (.+), (.-), (.*), (./), (.**)
  , min', max', log', div', mod', floor', ceil', round'
  , num
  , (.!!), (.!!!)
  -- * Comparison
  , (.<=), (.>=), (.<), (.>), (.==), (./=)
  -- * Logical operations
  , bool
  , (.&&), (.||), not'
  -- * Ternary operator
  --
  -- | @cond .? ifTrue .: ifFalse@ is similar to the ternary operator in C-like
  -- languages.  Since the Haskell syntax does not directly support mixfix
  -- operators, we mimic this form with two infix operators.
  , (.?), (.:)
  -- * Control flow
  , eval, block, if', when', switch, orElse
  -- * Compilation
  , compile, compileWith
  ) where

import Netter.Prob
import Netter.Var

import Netter.Options
import Netter.Pass
import qualified Netter.Prism.Expr as PE
import qualified Netter.Imp as Imp
import qualified Netter.Compiler as Compiler


import Data.Text hiding (length, foldr, zip)
import Control.Lens hiding ((.>))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Cont
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Key hiding (zip)

type Expr = PE.Expr

data S = S { _sVarDecls :: M.Map Var (Int, Int)
           , _sLocals   :: Set Var
           , _sRewards  :: M.Map Text Expr
           , _sComs     :: [Imp.Com] }

makeLenses ''S

type Builder = StateT S Pass

newtype Prog a = Prog {runProg :: ContT () Builder a}
  deriving (Applicative, Functor, Monad,
            MonadState S, MonadReader Options,
            MonadFresh, MonadCont)

liftProg :: Builder () -> Prog ()
liftProg = Prog . lift

unliftProg :: Prog () -> Builder ()
unliftProg (Prog p) = runContT p return

reset :: Prog () -> Prog ()
reset = liftProg . unliftProg

instance MonadError Result Prog where
  throwError = Prog . lift . throwError
  catchError (Prog f) h =
    Prog $ ContT
    $ \k -> catchError (runContT f k)
    $ \e -> runContT (runProg $ h e) k

-- | Inject integers into expressions.  Note that 'Expr' is an instance of
-- 'Num', so integer literals can be interpreted as expressions.
int :: Int -> Expr
int = PE.Const . PE.Int

-- | Inject floating-point numbers into expressions.
double :: Double -> Expr
double = PE.Const . PE.Double

-- | Inject booleans into expressions.
bool :: Bool -> Expr
bool = PE.Const . PE.Bool

{-# DEPRECATED num "Use int instead" #-}
num :: Int -> Expr
num = int

-- | @var lb ub@ creates a new integer variable in the interval @[lb .. ub]@.
-- Variables are always initialized to the lower bound of their interval.
var :: Int -> Int -> Prog Expr
var = namedVar "_"

-- | Similar to 'var', but allows us to choose the name of the variable output
-- in the Prism model.  Useful for debugging.
namedVar :: Text -> Int -> Int -> Prog Expr
namedVar x lb ub = do
  when (lb > ub) $ throwError $ Error $
    "Invalid bounds for variable " ++ unpack x ++ ": " ++
    show lb ++ ">" ++ show ub

  v <- fresh x

  sVarDecls.at v ?= (lb, ub)
  sLocals  .at v ?= ()

  return $ PE.Var v

ensureVar :: Expr -> Prog Var
ensureVar (PE.Var v) = do
  varDeclared <- uses sVarDecls (M.member v)

  unless varDeclared $ do
    throwError $ Error $ "Attempt to assign to an undeclared variable " ++ show v

  return v

ensureVar e =
  throwError $ Error $ "Attempt to assign to non-variable " ++ show e

-- | @v .<- e@ assigns the value of @e@ to the variable @v@.  If @v@ is some
-- expression other than a variable, the compiler throws an error.
infix 1 .<-
(.<-) :: Expr -> Expr -> Prog ()
e .<- rhs = do
  v <- ensureVar e
  sComs %= (Imp.Com [Imp.Assn (M.singleton v (return $ return rhs))] :)

-- | Return a uniform distribution over the values given by the expressions.
-- For example, the snippet @x .<-$ unif [1, 2, 3]@ assigns one of @1@, @2@ or
-- @3@ to @x@, each with a probability of @1/3@.
unif :: [Expr] -> [(Double, Expr)]
unif [] = error "Tried to take a uniform distribution over an empty list"
unif es = [(p, e) | e <- es]
  where p = 1 / fromIntegral (length es)

-- | Similar to '.<-', but the assigned value is chosen by sampling.  For
-- example, @v .<-$ [(0.3, 0), (0.7, 1)]@ sets @v@ to @0@ with probability
-- @0.3@, and to @1@ with probability @0.7@.  The probabilities must sum to one.
infix 1 .<-$
(.<-$) :: Expr -> [(Double, Expr)] -> Prog ()
e .<-$ rhs = do
  v <- ensureVar e
  sComs %= (Imp.Com [Imp.Assn (M.singleton v (return $ P rhs))] :)

-- | @rewards x e@ declares @x@ as a new reward.  Prism can check various
-- properties of rewards; e.g. their average stationary value, maximum, minimum,
-- etc.
rewards :: String -> Expr -> Prog ()
rewards x e = do
  redefining <- uses sRewards $ M.member $ pack x
  when redefining $ do
    throwError $ Error $ "Redefining reward " ++ x
  sRewards.at (pack x) ?= e

infix 1 .?
(.?) :: Expr -> Expr -> Expr -> Expr
e .? eThen = PE.If e eThen

infix 0 .:
(.:) :: (Expr -> Expr) -> Expr -> Expr
(.:) = id

flushCom :: MonadState S m => m () -> m Imp.Com
flushCom f = do
  coms0 <- use sComs
  sComs .= []
  f
  coms1 <- use sComs
  sComs .= coms0
  return $ Imp.revSeq coms1

addCom :: MonadState S m => Imp.Com -> m ()
addCom c = sComs %= (c :)

parEval :: [a] -> ([(a, Imp.Com)] -> Builder ()) -> Prog a
parEval xs k1 = Prog $ ContT $ \k0 -> do
  cs <- forM xs $ \x -> do
    c <- flushCom $ k0 x
    return (x, c)
  k1 cs

-- | Index into a list of expressions.
--
-- @
-- [e0 .. en] .!! e == (e .== 0 .? e1 .: .. e .== int n .? en .: 0)
-- @
--
-- Note that the result is zero if @e@ evaluates to an out-of-bounds index.

infixl 9 .!!

(.!!) :: (Key m ~ Int, FoldableWithKey m) => m Expr -> Expr -> Expr
xs .!! e =
  foldrWithKey (\i x acc -> (e .== int i) .? x .: acc) 0 xs

-- | Index into a list using an expression.  This is compiled using a series of
-- if statements: we test if the expression equals each possible index, and run
-- the continuation with the corresponding value at that index.  (*Warning*: if
-- the expression does not equal anything, the continuation is discarded.)  This
-- is quite inefficient in general, since it makes copies of the control-flow of
-- the program for each element on the list.  Whenever possible, you should use
-- the '.!!' operator instead, or limit the scope of the result with 'block'.

infixl 9 .!!!

(.!!!) :: (Key m ~ Int, FoldableWithKey m) => m a -> Expr -> Prog a
xs .!!! e = do
  (_, x) <- parEval (toKeyedList xs)
            $ \bs -> addCom $ Imp.switch [(e .== int i, c) | ((i, _), c) <- bs]
  return x


-- | Evaluate an expression so that it can be used as an integer inside of
-- Haskell.  We cannot know in advance what value the expression will take, so
-- the compilation strategy is very inefficient: we test whether the expression
-- is equal to each value it can take.  Thus, you should only use this function
-- if you know there isn't a way of deferring evaluation to the Prism side.

eval :: Expr -> Prog Int
eval e@(PE.Var v) = do
  bounds <- use $ sVarDecls.at v
  case bounds of
    Just (lb, ub) ->
      parEval [lb .. ub]
      $ \bs -> addCom $ Imp.switch [(e .== int i, c) | (i, c) <- bs]

    Nothing ->
      error $ "Undeclared variable " ++ show v

eval e = do
  error $ "Cannot evaluate non-variable yet (got " ++ show e ++ ")"

-- | Variables declared in a block are local and automatically deallocated when
-- the block finishes.  This can help reduce the state space of the generated
-- model.

block :: Prog () -> Prog ()
block b = do
  locals0 <- use sLocals
  sLocals .= S.empty
  c <- flushCom $ reset b
  locals1 <- use sLocals
  addCom (Imp.Com [Imp.Block locals1 c])
  sLocals .= locals0

-- | If statement
if' :: Expr -> Prog () -> Prog () -> Prog ()
if' e cThen cElse = do
  comThen <- flushCom $ block cThen
  comElse <- flushCom $ block cElse
  addCom $ Imp.Com [Imp.If e comThen comElse]

-- | A chain of if statements.  The command
-- @
-- switch [(c1, e1), ..., (cn, en), (orElse, eElse)]
-- @
-- is equivalent to
-- @
-- if' c1 e1 (... (if' cn en eElse) ...)
-- @
switch :: [(Expr, Prog ())] -> Prog ()
switch [] = return ()
switch ((cond, e) : branches) = if' cond e (switch branches)

-- | A synonym for @bool True@ to make 'switch' more readable.
orElse :: Expr
orElse = bool True

-- | Like 'if'', but without an else branch.
when' :: Expr -> Prog () -> Prog ()
when' e c = if' e c (return ())

-- | Round a number up to the nearest integer.
ceil' :: Expr -> Expr
ceil' = PE.UnOp PE.Ceil

-- | Round a number down to the nearest integer.
floor' :: Expr -> Expr
floor' = PE.UnOp PE.Floor

-- | Round a number to the nearest integer.
round' :: Expr -> Expr
round' = PE.UnOp PE.Round

-- | Maximum of two numbers.
max' :: Expr -> Expr -> Expr
max' = PE.BinOp PE.Max

-- | Minimum of two numbers.
min' :: Expr -> Expr -> Expr
min' = PE.BinOp PE.Min

-- | @mod' a b@ computes the remainder of the integer division of @a@ by @b@.
mod' :: Expr -> Expr -> Expr
mod' = PE.BinOp PE.Mod

-- | @log' a b@ returns the logarithm of @a@ in the base @b@.
log' :: Expr -> Expr -> Expr
log' = PE.BinOp PE.Log

-- | Logical and.
infixr 3 .&&
(.&&) :: Expr -> Expr -> Expr
(.&&) = PE.BinOp PE.And

-- | Logical or.
infixr 2 .||
(.||) :: Expr -> Expr -> Expr
(.||) = PE.BinOp PE.Or

-- | Negation
not' :: Expr -> Expr
not' = PE.UnOp PE.Not

-- | Multiplication.
infixl 7 .*
(.*) :: Expr -> Expr -> Expr
(.*) = PE.BinOp PE.Times

-- | @a .** b@ raises @a@ to the power @b@.
infix 8 .**
(.**) :: Expr -> Expr -> Expr
(.**) = PE.BinOp PE.Pow

-- | Floating-point division.
infixl 7 ./
(./) :: Expr -> Expr -> Expr
(./) = PE.BinOp PE.Div

-- | Integer division.
div' :: Expr -> Expr -> Expr
div' e1 e2 = floor' (e1 ./ e2)

-- | Addition.
infixl 6 .+
(.+) :: Expr -> Expr -> Expr
(.+) = PE.BinOp PE.Plus

-- | Subtraction.
infixl 6 .-
(.-) :: Expr -> Expr -> Expr
(.-) = PE.BinOp PE.Minus

-- | Equality test.
infix 4 .==
(.==) :: Expr -> Expr -> Expr
e1 .== e2 = PE.BinOp PE.Eq e1 e2

-- | Test if two values are different.
infix 4 ./=
(./=) :: Expr -> Expr -> Expr
e1 ./= e2 = PE.UnOp PE.Not (e1 .== e2)

-- | Compare numbers for ordering.
infix 4 .<=
(.<=) :: Expr -> Expr -> Expr
(.<=) = PE.BinOp PE.Leq

infix 4 .>=
(.>=) :: Expr -> Expr -> Expr
(.>=) = flip (.<=)

-- | Compare numbers for strict ordering.
infix 4 .<
(.<) :: Expr -> Expr -> Expr
(.<) = PE.BinOp PE.Lt

infix 4 .>
(.>) :: Expr -> Expr -> Expr
(.>) = flip (.<)

-- | Similar to 'compile', but reads the options from its first argument rather
-- than from the command line.
compileWith :: Options -> Prog () -> IO ()
compileWith opts (Prog prog) = doPass opts $ do
  let prog' = runContT prog $ \_ -> return ()
  ((), S decls _locals rews coms) <- runStateT prog' $ S M.empty S.empty M.empty []
  Compiler.compile (Imp.Program decls (PE.mklocals M.empty) rews (Imp.revSeq coms))

-- | Compile a program to Prism code, printing the result on standard output.
-- The behavior of the compiler can be tweaked by command-line options
-- (cf. 'Netter.Options.Options').
compile :: Prog () -> IO ()
compile prog = do
  opts <- readOptions
  compileWith opts prog
