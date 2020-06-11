module RandC.Dependencies where

import RandC.Var
import RandC.Prob       hiding (resolve)
import qualified RandC.G as G
import RandC.G          hiding (If, simplify)
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
        addExprDeps allDeps e = S.union allDeps (vars e)

-- | This dependency map, computed by @definitionStateDeps@ below, maps each
-- local definition to the set of state variables it depends on
type StateDeps = M.Map Var (S.Set Var)

definitionStateDeps :: M.Map Var Expr -> StateDeps
definitionStateDeps defs = foldl updateDependencies M.empty $ M.keysSet defs
  where directDepMap = M.map vars defs
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

class HasStateDeps a where
  stateDeps :: StateDeps -> a -> S.Set Var

-- | Lookup the dependencies of a variable.  If a variable does not appear on
-- the dependency map, it is supposed to be part of the program state instead of
-- a local definition.  In this case, the variable depends only on itself.
instance HasStateDeps Var where
  stateDeps deps v = M.findWithDefault (S.singleton v) v deps

instance HasStateDeps Expr where
  stateDeps deps e =
    S.unions [stateDeps deps v | v <- S.toList $ vars e]

instance HasStateDeps a => HasStateDeps (P a) where
  stateDeps deps e = S.unions $ fmap (stateDeps deps) e

instance HasStateDeps a => HasStateDeps (G a) where
  stateDeps deps (G.Return x) =
    stateDeps deps x
  stateDeps deps (G.If e x1 x2) =
    S.unions [stateDeps deps e, stateDeps deps x1, stateDeps deps x2]

instance HasStateDeps a => HasStateDeps [a] where
  stateDeps deps xs = S.unions $ map (stateDeps deps) xs

instance HasStateDeps Int where
  stateDeps _ _ = S.empty
