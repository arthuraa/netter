{-# LANGUAGE OverloadedStrings #-}
module RandC.Compiler.CFGToUPA where

import RandC.Var
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

compile :: Src.Program -> Pass Tgt.Program
compile prog = do
  Src.Program decls maxId blocks <- ensureTarget UPA prog
  pc <- fresh "pc"
  let check n = BinOp Eq (Var pc) (Const (Num n))
  let actions = [ (check n, fmap Tgt.Assn assns)
                | (n, Src.Block assns _) <- M.assocs blocks ]
  let varModule = Tgt.Module decls actions
  let pcAssn nextPc = M.singleton pc (compileNextPc nextPc)
  let pcActions = [ (check n, return $ Tgt.Assn $ pcAssn nextPc)
                  | (n, Src.Block _ nextPc) <- M.assocs blocks ]
  let pcModule = Tgt.Module (M.singleton pc (0, maxId - 1)) pcActions
  return (Tgt.Program M.empty [varModule, pcModule])
