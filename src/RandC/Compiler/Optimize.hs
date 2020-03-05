module RandC.Compiler.Optimize where

import RandC.Var
import RandC.Imp
import RandC.Prob       hiding (resolve)
import RandC.Pass
import qualified RandC.Prism.Expr as PE
import RandC.Prism.Expr hiding (If)

import Control.Monad.State
import Data.Maybe (isNothing)
import qualified Data.Set        as S
import qualified Data.Map.Strict as M

assnDeps :: M.Map Var (P Expr) -> S.Set Var
assnDeps assn =
  foldl addVarDeps S.empty assn
  where addVarDeps allDeps es = foldl addExprDeps allDeps es
        addExprDeps allDeps e = S.union allDeps (vars e)

type Ev a = StateT (M.Map Var Expr) Pass a

locally :: Ev a -> Ev (a, M.Map Var Expr)
locally f = do
  es <- get
  put M.empty
  res <- f
  es' <- get
  put es
  return (res, es')

evalExpr :: Expr -> Ev Expr
evalExpr = substM $ \v -> do
  es <- get
  return $ M.findWithDefault (Var v) v es

evalCom :: Com -> Ev Com
evalCom c = Com <$> evalInstrs (instrs c)

evalInstrs :: [Instr] -> Ev [Instr]
evalInstrs [] =
  return []
evalInstrs (i : is) = do
  i  <- evalInstr  i
  is <- evalInstrs is
  case i of
    Assn assns | assns == M.empty -> return is
    _ -> return $ i : is

evalInstr :: Instr -> Ev Instr
evalInstr (Assn assns) = do
  assns <- mapM (traverse evalExpr) assns
  let detAssns  = M.mapMaybe ofP assns
  let probAssns = M.filter (isNothing . ofP) assns
  modify (M.unionWith (\assn _ -> assn) detAssns)
  return $ Assn probAssns

evalInstr (If e cThen cElse) = do
  e <- evalExpr e
  (cThen, esThen) <- locally $ evalCom cThen
  (cElse, esElse) <- locally $ evalCom cElse

  forM_ (S.toList $ S.union (M.keysSet esThen) (M.keysSet esElse)) $ \v -> do
    let eThen = M.findWithDefault (Var v) v esThen
    let eElse = M.findWithDefault (Var v) v esElse
    unless (eThen == Var v && eElse == Var v) $
      modify $ M.insert v $ PE.If e eThen eElse

  return $ If e cThen cElse

extractLocals :: Program -> Pass Program
extractLocals (Program decls defs com) = do
  (Com is, es') <- runStateT (evalCom com) M.empty
  let is' = if es' == M.empty then is
            else is ++ [Assn $ M.map return es']
  return $ Program decls defs $ Com $ is'

optimize :: Program -> Pass Program
optimize prog = extractLocals prog
