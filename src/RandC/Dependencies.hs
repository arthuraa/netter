module RandC.Dependencies where

import RandC.Var
import RandC.Prob       hiding (resolve)
import qualified RandC.G as G
import RandC.G          hiding (If, simplify)
import qualified RandC.Prism.Expr as PE
import RandC.Prism.Expr hiding (If, simplify)

import qualified Data.Set        as S
import qualified Data.Map.Strict as M

-- | Various passes require computing the state variables that an expresion
-- depends on.  Computing this set is slightly tricky because of local
-- definitions.  If an expression uses a local definition, we have to find all
-- the state variables that this definition depends on.  Since a definition
-- might depend on another one, we have to compute the dependecies recursively.

-- | Compute all the variables that appear on the right-hand side of a parallel
-- assignment.
assnDeps :: M.Map Var (P Expr) -- ^ Assignment of probabistic expressions to variables.
         -> S.Set Var          -- ^ Variables on the right-hand side.
assnDeps assn =
  foldl addVarDeps S.empty assn
  where addVarDeps allDeps es = foldl addExprDeps allDeps es
        addExprDeps allDeps e = S.union allDeps (PE.vars e)

-- | This dependency map, computed by @definitionStateDeps@ below, maps each
-- local definition to the set of state variables it depends on
type StateDeps = M.Map Var (S.Set Var)

definitionStateDeps :: M.Map Var Expr -> StateDeps
definitionStateDeps defs = foldl updateDependencies M.empty $ M.keysSet defs
  where directDepMap = M.map PE.vars defs
        updateDependencies deps v
          | M.member v deps =
            -- The variable v has already been visited, so we can skip it
            deps
          | otherwise =
            let directDeps = M.findWithDefault S.empty v directDepMap
                toVisit    = S.difference directDeps (M.keysSet deps)
                stateDeps  = S.difference directDeps (M.keysSet defs)
                deps'      = foldl updateDependencies deps toVisit
                allDeps    = S.unions
                             $ stateDeps
                             : [ M.findWithDefault S.empty v' deps'
                               | v' <- S.toList directDeps ] in
              M.insert v allDeps deps'

-- | Lookup the dependencies of a variable.  If a variable does not appear on
-- the dependency map, it is supposed to be part of the program state instead of
-- a local definition.  In this case, the variable depends only on itself.
varStateDeps :: StateDeps -> Var -> S.Set Var
varStateDeps deps v = M.findWithDefault (S.singleton v) v deps

exprStateDeps :: StateDeps -> Expr -> S.Set Var
exprStateDeps deps e =
  S.unions [varStateDeps deps v | v <- S.toList $ PE.vars e]

probExprStateDeps :: StateDeps -> P Expr -> S.Set Var
probExprStateDeps deps e = S.unions $ fmap (exprStateDeps deps) e

guardedStateDeps :: StateDeps -> (StateDeps -> a -> S.Set Var) -> G a -> S.Set Var
guardedStateDeps deps f e =
  let innerStateDeps  = S.unions $ fmap (f deps) e
      branchDeps      = G.vars (const S.empty) e
      branchStateDeps = S.unions $ S.map (varStateDeps deps) branchDeps in
    innerStateDeps `S.union` branchStateDeps

guardedExprStateDeps :: StateDeps -> G (P Expr) -> S.Set Var
guardedExprStateDeps deps e = guardedStateDeps deps probExprStateDeps e
