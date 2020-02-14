module RandC.Compiler.UPAToPrism where

import qualified RandC.Prism.Expr as E
import qualified RandC.UPA   as Src
import qualified RandC.Prism as Tgt

import qualified Data.Map as M

compileModule :: (Int, Src.Module) -> Tgt.Module
compileModule (id, (decls, distr)) =
  let decls' = [Tgt.VarDecl v lb ub | (v, (lb, ub)) <- M.assocs decls]

      assns es = [Tgt.Assn v e | (v, e) <- M.assocs es]

      trans = Tgt.Transition (E.Const (E.Bool True)) in

    Tgt.Module id decls' [trans $ assns `fmap` distr]

compile :: Src.Program -> Tgt.Program
compile (Src.Program defs mods) =
  let defs' = [Tgt.Formula v e | (v, e) <- M.assocs defs]
      mods' = map compileModule $ zip [0..] mods in
  Tgt.Program defs' mods'