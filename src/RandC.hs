{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

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

module RandC (
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
  -- * Variables, formulas and rewards
  , namedVar
  , var
  , formula
  , rewards
  -- * Arithmetic expressions
  , int
  , double
  , (.<-), (.<-$), unif
  , (.+), (.-), (.*), (./), (.**)
  , min', max', log', div', mod', floor', ceil', round'
  , num
  -- * Comparison
  , (.<=), (.<), (.==), (./=)
  -- * Logical operations
  , bool
  , (.&&), (.||)
  -- * Ternary operator
  --
  -- | @cond .? ifTrue .: ifFalse@ is similar to the ternary operator in C-like
  -- languages.  Since the Haskell syntax does not directly support mixfix
  -- operators, we mimic this form with two infix operators.
  , (.?), (.:)
  -- * Control flow
  , block, if', when', switch, orElse
  -- * Compilation
  , compile, compileWith
  ) where

import RandC.Prob
import RandC.Var

import RandC.Options
import RandC.Pass
import qualified RandC.Prism.Expr as PE
import qualified RandC.Imp as Imp
import qualified RandC.Compiler as Compiler

import Data.Text hiding (length)
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as S

type Expr = PE.Expr

data S = S { sVarDecls :: M.Map Var (Int, Int)
           , sLocals   :: Set Var
           , sFormulas :: M.Map Var Expr
           , sRewards  :: M.Map Text Expr
           , sComs     :: [Imp.Com] }

type Prog a = StateT S Pass a

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

  modify $ \S{..} -> S{sVarDecls = M.insert v (lb, ub) sVarDecls,
                       sLocals   = S.insert v sLocals, ..}

  return $ PE.Var v

-- | @v .<- e@ assigns the value of @e@ to the variable @v@.  If @v@ is some
-- expression other than a variable, the compiler throws an error.
infix 1 .<-
(.<-) :: Expr -> Expr -> Prog ()
PE.Var v .<- rhs = do
  S{..} <- get

  when (not $ M.member v sVarDecls) $ do
    throwError $ Error $ "Attempt to assign to a non-variable " ++ show v

  put $ S{sComs = Imp.Com [Imp.Assn (M.singleton v (return $ return rhs))] : sComs, ..}

e .<- _rhs = throwError $ Error $ "Attempt to assign to non-variable " ++ show e

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
PE.Var v .<-$ rhs = do
  S{..} <- get

  when (not $ M.member v sVarDecls) $ do
    throwError $ Error $ "Attempt to assign to a non-variable " ++ show v

  put $ S{sComs = Imp.Com [Imp.Assn (M.singleton v (return $ P rhs))] : sComs, ..}

e .<-$ _rhs = throwError $ Error $ "Attempt to assign to non-variable " ++ show e

-- | @formula f e@ creates a formula @f@ in the Prism model that evaluates to
-- @e@.  Note that the value of a formula is computed where it is used, not
-- where it is defined.  For example, in the following program, the final value
-- of @y@ is @1@, not @0@.
--
-- @
-- x  <- var 0 10
-- y  <- var 0 10
-- x .<- 0
-- f  <- formula "f" x
-- x .<- 1
-- y  <- f
-- @
formula :: Text -> Expr -> Prog Expr
formula x e = do
  v <- fresh x

  modify $ \S{..} -> S{sFormulas = M.insert v e sFormulas, ..}

  return $ PE.Var v

-- | @rewards x e@ declares @x@ as a new reward.  Prism can check various
-- properties of rewards; e.g. their average stationary value, maximum, minimum,
-- etc.
rewards :: String -> Expr -> Prog ()
rewards x e = do
  let x' = pack x

  S{..} <- get

  case M.lookup x' sRewards of
    Just _  -> throwError $ Error $ "Redefining reward " ++ unpack x'
    Nothing -> put S{sRewards = M.insert x' e sRewards, ..}

infix 1 .?
(.?) :: Expr -> Expr -> Expr -> Expr
e .? eThen = PE.If e eThen

infix 0 .:
(.:) :: (Expr -> Expr) -> Expr -> Expr
(.:) = id

-- | Variables declared in a block are local and automatically deallocated when
-- the block finishes.  This can help reduce the state space of the generated
-- model.

block :: Prog () -> Prog ()
block f = do
  S{sLocals = sLocals0, ..} <- get
  put S{sLocals = S.empty, ..}
  f
  S{sLocals = sLocals1, ..} <- get
  forM_ (S.toList sLocals1) $ \v ->
    let (lb, _) = sVarDecls M.! v in
      PE.Var v .<- int lb
  put S{sLocals = sLocals0, ..}

-- | If statement
if' :: Expr -> Prog () -> Prog () -> Prog ()
if' e cThen cElse = do
  S decls locals defs rews coms <- get

  put $ S decls locals defs rews []
  cThen

  S decls' localsThen defsThen rewsThen comsThen <- get

  put $ S decls' localsThen defsThen rewsThen []
  cElse

  S decls'' localsElse defsElse rewsElse comsElse <- get

  let coms' = Imp.Com [Imp.If e (Imp.revSeq comsThen) (Imp.revSeq comsElse)] : coms

  put $ S decls'' localsElse defsElse rewsElse coms'

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

-- | Compare numbers for strict ordering.
infix 4 .<
(.<) :: Expr -> Expr -> Expr
(.<) = PE.BinOp PE.Lt

-- | Similar to 'compile', but reads the options from its first argument rather
-- than from the command line.
compileWith :: Options -> Prog () -> IO ()
compileWith opts prog = doPass opts $ do
  ((), S decls _locals defs rews coms) <- runStateT prog $ S M.empty S.empty M.empty M.empty []
  Compiler.compile (Imp.Program decls defs rews (Imp.revSeq coms))

-- | Compile a program to Prism code, printing the result on standard output.
-- The behavior of the compiler can be tweaked by command-line options
-- (cf. 'RandC.Options.Options').
compile :: Prog () -> IO ()
compile prog = do
  opts <- readOptions
  compileWith opts prog
