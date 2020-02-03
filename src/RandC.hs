module RandC where

import RandC.P
import RandC.Var
import RandC.Prism.Expr
import qualified RandC.Imp as Imp

import Data.Functor.Identity
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as M

data S = S { sVarDecls :: M.Map Var (Int, Int)
           , sVarCount :: Int
           , sComs :: [Imp.Com] }

type Comp a = ExceptT String (StateT S Identity) a

var :: Int -> Int -> Comp Expr
var lb ub = do
  when (lb > ub) $ throwError $
    "Invalid bounds for variable: " ++ show lb ++ ">" ++ show ub

  S decls count coms <- get

  let v = Unnamed count
  let decls' = M.insert v (lb, ub) decls

  put $ S decls' (count + 1) coms

  return $ Var v

-- Assignment operator used for Var
infix 1 .<-
(.<-) :: Expr -> Expr -> Comp ()
Var v .<- rhs = do
  S decls count coms <- get
  put $ S decls count (Imp.Assn v rhs : coms)

e .<- rhs = throwError $ "Attempt to assign to non-variable " ++ show e

infix 1 .<-$
(.<-$) :: Expr -> [(Double, Expr)] -> Comp ()
Var v .<-$ rhs = do
  S decls count coms <- get
  put $ S decls count (Imp.Choice v (P rhs) : coms)

e .<-$ rhs = throwError $ "Attempt to assign to non-variable " ++ show e

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

when' :: Expr -> Comp () -> Comp ()
when' e c = if' e c (return ())

runComp :: Comp a -> (Either String a, S)
runComp prog =
  runIdentity $ runStateT (runExceptT prog) $ S M.empty 0 []

compile :: Comp () -> IO ()
compile prog = do
  let (res, S decls _ coms) = runComp prog
  case res of
    Left error -> putStrLn $ "Error: " ++ error
    Right _ -> do
      print decls
      print coms
