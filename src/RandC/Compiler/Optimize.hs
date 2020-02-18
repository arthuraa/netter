module RandC.Compiler.Optimize where

import RandC.Var
import RandC.Options
import RandC.Pass
import RandC.Prob
import qualified RandC.Prism.Expr as PE
import qualified RandC.SSA2       as SSA2

import Control.Monad.Reader
import qualified Data.Map.Strict as M

doSimplify :: SSA2.Assn -> SSA2.Defs -> (SSA2.Assn, SSA2.Defs)
doSimplify assn defs =
  (M.map (prune . fmap PE.simplify) assn, M.map PE.simplify defs)

doInlining :: SSA2.Assn -> SSA2.Defs -> (Bool, SSA2.Assn, SSA2.Defs)
doInlining assn defs =
  let count :: (Foldable t) => t (M.Map Var Int) -> M.Map Var Int
      count      = foldl (|+|) M.empty
      assnCounts = count $ M.map (count . fmap PE.counts) assn
      defsCounts = count $ M.map PE.counts defs
      cs         = assnCounts |+| defsCounts

      substAssn :: Var -> PE.Expr -> D PE.Expr -> D PE.Expr
      substAssn v e e' =
        PE.subst1M v (return e) =<< e'

      canInline v e =
        M.findWithDefault 0 v cs <= 1 || PE.atomic e

      scan (changed, assn, defs) v =
        case M.lookup v defs of
          Just e ->
            if canInline v e then
              let assn' = M.map (substAssn v e) assn
                  defs' = M.map (PE.subst1 v e) (M.delete v defs) in
                (True, assn', defs')
            else (changed, assn, defs)
          Nothing -> (changed, assn, defs)

  in foldl scan (False, assn, defs) $ M.keysSet defs

optimize :: Bool -> Bool -> SSA2.Assn -> SSA2.Defs -> (SSA2.Assn, SSA2.Defs)
optimize simplify inlining assn defs =
  let (assn1, defs1) =
        if simplify then doSimplify assn defs else (assn, defs)
      (changed, assn2, defs2) =
        if inlining then doInlining assn1 defs1 else (False, assn1, defs1) in
    if changed then optimize simplify inlining assn2 defs2
    else (assn2, defs2)

compile :: SSA2.Program -> Pass SSA2.Program
compile (SSA2.Program decls dice assn defs) = do
  inlining <- reader inlining
  simplify <- reader simplify
  let (assn', defs') = optimize simplify inlining assn defs
  return $ SSA2.Program decls dice assn' defs'
