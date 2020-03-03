{-# LANGUAGE OverloadedStrings #-}
module RandC.Compiler.CFGToUPA where

import RandC.Var
import RandC.Prob
import RandC.Options
import RandC.G as G
import RandC.Pass
import RandC.Prism.Expr as PE
import qualified RandC.CFG as Src
import qualified RandC.UPA as Tgt

import qualified Data.Map as M

compileNextPc :: G Src.Id -> Expr
compileNextPc (G.Return id) = Const $ Num id
compileNextPc (G.If e e1 e2) = PE.If e (compileNextPc e1) (compileNextPc e2)

type Assn = M.Map Var (M.Map Src.Id (P Expr))

updateAssn :: Assn -> Src.Id -> Src.Block -> Assn
updateAssn assns id block =
  M.foldlWithKey addAssn assns (Src.bAssn block)
  where addAssn assns v e =
          let vAssns = M.findWithDefault M.empty v assns in
            M.insert v (M.insert id e vAssns) assns

compile :: Src.Program -> Pass Tgt.Program
compile prog = do
  Src.Program decls maxId blocks <- ensureTarget UPA prog
  pc <- fresh "pc"
  let assns = M.foldlWithKey updateAssn M.empty blocks
  let checkPc n = BinOp Eq (Var pc) (Const (Num n))
  let varActions v = [ (checkPc n, fmap (Tgt.Assn . M.singleton v) e)
                     | (n, e) <- M.assocs $ M.findWithDefault M.empty v assns ]
  let varModules = [ Tgt.Module (M.singleton v (lb, ub)) (varActions v)
                   | (v, (lb, ub)) <- M.assocs decls ]
  let pcAssn nextPc = M.singleton pc (PE.simplify $ compileNextPc nextPc)
  let pcActions = [ (checkPc n, return $ Tgt.Assn $ pcAssn nextPc)
                  | (n, Src.Block _ nextPc) <- M.assocs blocks ]
  let pcModule = Tgt.Module (M.singleton pc (0, maxId - 1)) pcActions
  return $ Tgt.Program M.empty (pcModule : varModules)
