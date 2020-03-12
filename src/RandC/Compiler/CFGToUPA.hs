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

import qualified Data.Set        as S
import qualified Data.Map.Strict as M

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

  Src.Program decls defs maxId blocks <- ensureTarget UPA prog

  pc <- fresh "pc"

  let decls'  = M.insert pc (0, maxId - 1) decls

  let pcAssns = M.fromList [ (n, return $ PE.simplify $ compileNextPc nextPc)
                           | (n, Src.Block _ nextPc) <- M.assocs blocks ]

  let assnMap = M.foldlWithKey updateAssn (M.singleton pc pcAssns) blocks

  let checkPc n = BinOp Eq (Var pc) (Const (Num n))

  let allPCs  = S.fromList [0 .. maxId - 1]

  let actions v =
        let assns        = M.findWithDefault M.empty v assnMap
            constantPCs  = S.difference allPCs $ M.keysSet assns
            defaultGuard =
              if constantPCs == S.empty then []
              else [conj [UnOp Not $ checkPc n | n <- M.keys assns]] in
          [ (guard, return $ Tgt.Assn M.empty) | guard <- defaultGuard ] ++
          [ (checkPc n, fmap (Tgt.Assn . M.singleton v) e)
          | (n, e) <- M.assocs assns ]

  let modules = [ Tgt.Module (M.singleton v (lb, ub)) (actions v)
                | (v, (lb, ub)) <- M.assocs decls' ]

  return $ Tgt.Program defs modules
