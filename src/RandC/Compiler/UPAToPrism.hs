module RandC.Compiler.UPAToPrism where

import RandC.Pass
import RandC.Prism.Expr

import qualified RandC.UPA   as Src
import qualified RandC.Prism as Tgt

import qualified Data.Map.Strict as M

compileAssn :: Src.Assn -> Tgt.Assns
compileAssn (Src.Assn assn) =
  Tgt.Assns [Tgt.Assn v e | (v, e) <- M.assocs assn]

compileModule :: (Int, Src.Module) -> Tgt.Module
compileModule (id, Src.Module decls trans) =
  let decls' = [Tgt.VarDecl v lb ub | (v, (lb, ub)) <- M.assocs decls]

      trans' = [Tgt.Transition guard (compileAssn <$> assns)
               |(guard, assns) <- trans]

      -- Default case: no modifications
      def = foldl (BinOp And) (Const (Bool True)) [UnOp Not $ fst t | t <- trans] in

    Tgt.Module id decls' (trans' ++ [Tgt.Transition def $ return $ Tgt.Assns []])

compile :: Src.Program -> Pass Tgt.Program
compile (Src.Program defs mods) =
  let defs' = [Tgt.Formula v e | (v, e) <- M.assocs defs]
      mods' = map compileModule $ zip [0..] mods in
  return $ Tgt.Program defs' mods'
