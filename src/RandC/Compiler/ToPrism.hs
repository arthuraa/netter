module RandC.Compiler.ToPrism where

import RandC.Var
import RandC.P
import qualified RandC.Prism.Expr as E
import RandC.Prism

import qualified Data.Map as M
import qualified Data.Set as S

compileModule ::
  M.Map Var (Int, Int) -> Int -> (S.Set Var, P (M.Map Var E.Expr)) -> Module
compileModule decls id (vs, distr) =
  let bounds v = case M.lookup v decls of
                   Just bs -> bs
                   Nothing -> error "Variable does not have bounds"

      decls' = [VarDecl v lb ub | v <- S.toList vs, let (lb, ub) = bounds v]

      assns es = [Assn v e | (v, e) <- M.assocs es] in

    Module id decls' [Transition (E.Const (E.Bool True)) $ assns `fmap` distr]

compile ::
  M.Map Var (Int, Int) -> [(S.Set Var, P (M.Map Var E.Expr))] -> Program
compile decls mods =
  Program [compileModule decls i mod | (i, mod) <- zip [0..] mods]
