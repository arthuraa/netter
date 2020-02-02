module RandC where

import RandC.P
import RandC.Var
import RandC.Expr
import RandC.RandImp

import Data.Functor.Identity
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as M

data Program = Program { pVarDecls :: M.Map Var (Int, Int)
                       , pVarCount :: Int
                       , pComs :: [Com] }

type Comp a = ExceptT String (StateT Program Identity) a

revSeq :: [Com] -> Com
revSeq [] = Skip
revSeq [c] = c
revSeq (c : coms) = Seq (revSeq coms) c

var :: Int -> Int -> Comp Expr
var lb ub = do
  when (lb > ub) $ throwError $
    "Invalid bounds for variable: " ++ show lb ++ ">" ++ show ub

  Program decls count coms <- get

  let v = Unnamed count
  let decls' = M.insert v (lb, ub) decls

  put $ Program decls' (count + 1) coms

  return $ Var v

-- Assignment operator used for Var
infix 1 .<-
(.<-) :: Expr -> Expr -> Comp ()
Var v .<- rhs = do
  Program decls count coms <- get
  put $ Program decls count (Assn v rhs : coms)

e .<- rhs = throwError $ "Attempt to assign to non-variable " ++ show e

infix 1 .<-$
(.<-$) :: Expr -> [(Double, Expr)] -> Comp ()
Var v .<-$ rhs = do
  Program decls count coms <- get
  let choices = [(p, Assn v e) | (p, e) <- rhs]
  put $ Program decls count (Choice (P choices) : coms)

e .<-$ rhs = throwError $ "Attempt to assign to non-variable " ++ show e

if' :: Expr -> Comp () -> Comp () -> Comp ()
if' e cThen cElse = do
  Program decls count coms <- get

  put $ Program decls count []
  cThen

  Program decls' count' comsThen <- get

  put $ Program decls' count' []
  cElse

  Program decls'' count'' comsElse <- get

  put $ Program decls'' count'' (If e (revSeq comsThen) (revSeq comsElse) : coms)

when' :: Expr -> Comp () -> Comp ()
when' e c = if' e c (return ())

runComp :: Comp a -> (Either String a, Program)
runComp prog =
  runIdentity $ runStateT (runExceptT prog) $ Program M.empty 0 []

compile :: Comp () -> IO ()
compile prog = do
  let (res, Program decls _ coms) = runComp prog
  case res of
    Left error -> putStrLn $ "Error: " ++ error
    Right _ -> do
      print decls
      print coms
