module RandC.Compiler.Optimize where

import RandC.Var
import RandC.Options
import RandC.Pass
import RandC.Prob
import qualified RandC.Prism.Expr as PE
import qualified RandC.SSA2       as SSA2

import Control.Monad.Reader
import qualified Data.Map.Strict as M

inline :: Bool -> SSA2.Assn -> SSA2.Defs -> (SSA2.Assn, SSA2.Defs)
inline simplify assn defs =
  let count :: (Foldable t) => t (M.Map Var Int) -> M.Map Var Int
      count      = foldl (|+|) M.empty
      assnCounts = count $ M.map (count . fmap PE.counts) assn
      defsCounts = count $ M.map PE.counts defs
      cs         = assnCounts |+| defsCounts

      substAssn :: Var -> PE.Expr -> D PE.Expr -> D PE.Expr
      substAssn v e e' =
        e' >>= PE.subst1M v (return e)

      canInline v e =
        M.findWithDefault 0 v cs <= 1 || PE.atomic e

      scan (changed, assn, defs) v e =
        if canInline v e then
          let assn' = M.map (substAssn v e) assn
              defs' = M.map (PE.subst1 v e) (M.delete v defs) in
            (True, assn', defs')
        else (changed, assn, defs)

      (changed, assn', defs') = M.foldlWithKey scan (False, assn, defs) defs

      (assn'', defs'') =
        if simplify then
          (M.map (prune . fmap PE.simplify) assn', M.map PE.simplify defs')
        else (assn', defs')

  in
    if changed then inline simplify assn'' defs'' else (assn'', defs'')

compile :: SSA2.Program -> Pass SSA2.Program
compile prog@(SSA2.Program decls dice assn defs) = do
  inlining <- reader inlining
  simplify <- reader simplify
  if inlining then
    let (assn', defs') = inline simplify assn defs in
    return $ SSA2.Program decls dice assn' defs'
  else return prog
