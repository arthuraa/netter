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
           , sComs :: [Imp.Com] }

type Comp a = ExceptT String (VarGenT (StateT S Identity)) a

num :: Int -> Expr
num = PE.Const . PE.Num

namedVar :: String -> Int -> Int -> Comp Expr
namedVar x lb ub = do
  when (lb > ub) $ throwError $
    "Invalid bounds for variable " ++ x ++ ": " ++
    show lb ++ ">" ++ show ub

  v <- fresh x

  S decls coms <- get

  let decls' = M.insert v (lb, ub) decls

  put $ S decls' coms

  return $ PE.Var v

var :: Int -> Int -> Comp Expr
var = namedVar "_"

-- Assignment operator used for Var
infix 1 .<-
(.<-) :: Expr -> Expr -> Comp ()
PE.Var v .<- rhs = do
  S decls coms <- get
  put $ S decls (Imp.Assn v rhs : coms)

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
  S decls coms <- get
  put $ S decls (Imp.Choice v (P rhs) : coms)

e .<-$ _rhs = throwError $ "Attempt to assign to non-variable " ++ show e

if' :: Expr -> Comp () -> Comp () -> Comp ()
if' e cThen cElse = do
  S decls coms <- get

  put $ S decls []
  cThen

  S decls' comsThen <- get

  put $ S decls' []
  cElse

  S decls'' comsElse <- get

  put $ S decls'' (Imp.If e (Imp.revSeq comsThen) (Imp.revSeq comsElse) : coms)

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

runComp :: Comp a -> (Imp.Program -> VarGen b) -> (Either String b)
runComp prog f =
  let prog'  = runVarGenT (runExceptT prog) novars in
  let prog'' = runStateT  prog' $ S M.empty []  in
  let ((res, vars), S decls coms)  = runIdentity prog'' in
  case res of
    Left error -> Left error
    Right _ ->
      let prog = Imp.Program decls (Imp.revSeq coms)
          (tprog, _) = runIdentity $ runVarGenT (f prog) vars in
        Right tprog

compile :: Comp () -> IO ()
compile prog =
  case runComp prog Compiler.compile of
    Left error -> putStrLn $ "Error: " ++ error
    Right tprog -> putStrLn $ toSource tprog
