module RandC.Compiler.UPAToPrism where

import RandC.Pass
import qualified RandC.Prism.Expr as E
import qualified RandC.UPA   as Src
import qualified RandC.Prism as Tgt

import qualified Data.Map.Strict as M

compileModule :: (Int, Src.Module) -> Tgt.Module
compileModule (id, Src.Module decls distr) =
  let decls' = [Tgt.VarDecl v lb ub | (v, (lb, ub)) <- M.assocs decls]

      assns (Src.Assn es) = [Tgt.Assn v e | (v, e) <- M.assocs es]

      trans = Tgt.Transition (E.Const (E.Bool True)) in

    Tgt.Module id decls' [trans $ assns `fmap` distr]

compile :: Src.Program -> Pass Tgt.Program
compile (Src.Program defs mods) =
  let defs' = [Tgt.Formula v e | (v, e) <- M.assocs defs]
      mods' = map compileModule $ zip [0..] mods in
  return $ Tgt.Program defs' mods'
