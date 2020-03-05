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

type St a = StateT (M.Map Var Expr, M.Map Var Var) Pass a

localize :: Var -> Expr -> St ()
localize v e = do
  (locals, renamings) <- get
  v' <- fresh $ name v
  put (M.insert v' e locals, M.insert v v' renamings)

resolve :: Expr -> St Expr
resolve = substM $ \v -> do
  (_, renamings) <- get
  return $ Var $ M.findWithDefault v v renamings

restore :: St a -> St (a, M.Map Var Var)
restore f = do
  (_, renamings) <- get
  res <- f
  (locals, renamings') <- get
  put (locals, renamings)
  return (res, renamings')

extractLocalsCom :: Com -> St Com
extractLocalsCom c = Com <$> extractLocalsInstrs (instrs c)

extractLocalsInstrs :: [Instr] -> St [Instr]
extractLocalsInstrs [] =
  return []
extractLocalsInstrs (i : is) = do
  i  <- extractLocalsInstr  i
  is <- extractLocalsInstrs is
  case i of
    Assn assns | assns == M.empty -> return is
    _ -> return $ i : is

extractLocalsInstr :: Instr -> St Instr
extractLocalsInstr (Assn assns) = do
  assns <- mapM (traverse resolve) assns
  let detAssns  = M.mapMaybe ofP assns
  let probAssns = M.filter (isNothing . ofP) assns
  _ <- M.traverseWithKey localize detAssns
  return $ Assn probAssns

extractLocalsInstr (If e cThen cElse) = do
  e <- resolve e
  (cThen, vsThen) <- restore $ extractLocalsCom cThen
  (cElse, vsElse) <- restore $ extractLocalsCom cElse

  forM_ (S.toList $ S.union (M.keysSet vsThen) (M.keysSet vsElse)) $ \v -> do
    let vThen = M.findWithDefault v v vsThen
    let vElse = M.findWithDefault v v vsElse
    unless (vThen == v && vElse == v) $
      localize v $ PE.If e (Var vThen) (Var vElse)

  return $ If e cThen cElse

extractLocals :: Program -> Pass Program
extractLocals (Program decls defs com) = do
  (Com is, (defs', vars')) <- runStateT (extractLocalsCom com) (defs, M.empty)
  let is' = if vars' == M.empty then is
            else is ++ [Assn $ M.map (return . Var) vars']
  return $ Program decls defs' $ Com $ is'

optimize :: Program -> Pass Program
optimize prog = extractLocals prog
