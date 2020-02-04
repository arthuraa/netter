module RandC where

import RandC.P
import RandC.Var
import RandC.ToSource
import qualified RandC.Prism.Expr as PE
import qualified RandC.Imp as Imp
import qualified RandC.Compiler as Compiler

import Data.Functor.Identity
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as M

type Expr = PE.Expr

data S = S { sVarDecls :: M.Map Var (Int, Int)
           , sVarCount :: Int
           , sComs :: [Imp.Com] }

type Comp a = ExceptT String (StateT S Identity) a

num :: Int -> Expr
num = PE.Const . PE.Num

var :: Int -> Int -> Comp Expr
var lb ub = do
  when (lb > ub) $ throwError $
    "Invalid bounds for variable: " ++ show lb ++ ">" ++ show ub

  S decls count coms <- get

  let v = Unnamed count
  let decls' = M.insert v (lb, ub) decls

  put $ S decls' (count + 1) coms

  return $ PE.Var v

-- Assignment operator used for Var
infix 1 .<-
(.<-) :: Expr -> Expr -> Comp ()
PE.Var v .<- rhs = do
  S decls count coms <- get
  put $ S decls count (Imp.Assn v rhs : coms)

e .<- _rhs = throwError $ "Attempt to assign to non-variable " ++ show e

infix 1 .?
(.?) :: Expr -> Expr -> Expr -> Expr
e .? eThen = PE.If e eThen

infix 0 .:
(.:) :: (Expr -> Expr) -> Expr -> Expr
(.:) = id

infix 1 .<-$
(.<-$) :: Expr -> [(Double, Expr)] -> Comp ()
PE.Var v .<-$ rhs = do
  S decls count coms <- get
  put $ S decls count (Imp.Choice v (P rhs) : coms)

e .<-$ _rhs = throwError $ "Attempt to assign to non-variable " ++ show e

if' :: Expr -> Comp () -> Comp () -> Comp ()
if' e cThen cElse = do
  S decls count coms <- get

  put $ S decls count []
  cThen

  S decls' count' comsThen <- get

  put $ S decls' count' []
  cElse

  S decls'' count'' comsElse <- get

  put $ S decls'' count'' (Imp.If e (Imp.revSeq comsThen) (Imp.revSeq comsElse) : coms)

switch :: [(Expr, Comp ())] -> Comp ()
switch [] = return ()
switch ((cond, e) : branches) = if' cond e (switch branches)

orElse :: Expr
orElse = PE.Const (PE.Bool True)

when' :: Expr -> Comp () -> Comp ()
when' e c = if' e c (return ())

max' :: Expr -> Expr -> Expr
max' = PE.BinOp PE.Max

min' :: Expr -> Expr -> Expr
min' = PE.BinOp PE.Min

mod' :: Expr -> Expr -> Expr
mod' = PE.BinOp PE.Mod

infixr 3 .&&
(.&&) :: Expr -> Expr -> Expr
(.&&) = PE.BinOp PE.And

infixr 2 .||
(.||) :: Expr -> Expr -> Expr
(.||) = PE.BinOp PE.Or

infixl 7 .*
(.*) :: Expr -> Expr -> Expr
(.*) = PE.BinOp PE.Times

infixl 7 ./
(./) :: Expr -> Expr -> Expr
(./) = PE.BinOp PE.Div

infixl 6 .+
(.+) :: Expr -> Expr -> Expr
(.+) = PE.BinOp PE.Plus

infixl 6 .-
(.-) :: Expr -> Expr -> Expr
(.-) = PE.BinOp PE.Minus

-- Overload equal sign with @.==@
infix 4 .==
(.==) :: Expr -> Expr -> Expr
e1 .== e2 = PE.BinOp PE.Eq e1 e2

infix 4 ./=
(./=) :: Expr -> Expr -> Expr
e1 ./= e2 = PE.UnOp PE.Not (e1 .== e2)

infix 4 .<=
(.<=) :: Expr -> Expr -> Expr
(.<=) = PE.BinOp PE.Leq

infix 4 .<
(.<) :: Expr -> Expr -> Expr
(.<) = PE.BinOp PE.Lt

runComp :: Comp a -> (Either String a, S)
runComp prog =
  runIdentity $ runStateT (runExceptT prog) $ S M.empty 0 []

compile :: Comp () -> IO ()
compile prog = do
  let (res, S decls _ coms) = runComp prog
  case res of
    Left error -> putStrLn $ "Error: " ++ error
    Right _ ->
      let prog = Imp.Program decls (Imp.revSeq coms) in
      putStrLn $ toSource $ Compiler.compile prog
