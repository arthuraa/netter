module RandC.Compiler.SSA2ToSSA3 where

import RandC.Var
import RandC.Pass
import RandC.D
import qualified RandC.Prism.Expr as PE
import qualified RandC.SSA2 as Src
import qualified RandC.SSA3 as Tgt

import qualified Data.Map as M
import qualified Data.Set as S

varDeps :: Src.Defs -> Var -> S.Set Var
varDeps es v = go S.empty [v]
  where go visited [] =
          visited
        go visited (v : queue) =
          let visited'   = S.insert v visited
              directDeps = case M.lookup v es of
                             Just e  -> foldl S.union S.empty $ fmap PE.vars e
                             Nothing -> S.empty
              toVisit    = directDeps `S.difference` visited' in
            go visited' $ S.toList toVisit ++ queue

dieDeps :: Src.Defs -> Var -> S.Set Die
dieDeps es v =
  S.unions [ds v' | v' <- S.toList $ varDeps es v]
  where ds v' = case M.lookup v' es of
                  Just e -> dice e
                  Nothing -> S.empty

-- This function should terminate because the definition map es does not contain
-- loops.
subst :: M.Map Var (D PE.Expr) -> PE.Expr -> D PE.Expr
subst es e = doExpr e
  where doExpr  = PE.substM doVar
        doVar v = case M.lookup v es of
                    Just e' -> doExpr =<< e'
                    Nothing -> return $ PE.Var v

inline :: Src.Assn -> Src.Defs -> (Tgt.Assn, Tgt.Defs)
inline assn defs =
  let checkVar (detVars, probVars) v e
        | dieDeps defs v == S.empty =
          case e of
            Return e -> (M.insert v e detVars, probVars)
            _        -> error "SSA2ToSSA3: Die dependencies were incorrect"
        | otherwise =
          (detVars, M.insert v e probVars)

      (detVars, probVars) =
        M.foldlWithKey checkVar (M.empty, M.empty) defs

      unfoldAssn v' =
        subst probVars $ PE.Var v'

      assn' =
        M.map unfoldAssn assn
  in
    (M.map (fmap PE.simplify) assn', M.map PE.simplify detVars)

compile :: Src.Program -> Pass Tgt.Program
compile (Src.Program decls ds assn defs) =
  let (assn', defs') = inline assn defs in
  return $ Tgt.Program decls ds assn' defs'
