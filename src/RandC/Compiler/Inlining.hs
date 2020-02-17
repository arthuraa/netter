module RandC.Compiler.Inlining where

import RandC.Var
import RandC.Options
import RandC.Pass
import RandC.D
import qualified RandC.Prism.Expr as PE
import qualified RandC.SSA3       as SSA3

import Control.Monad.Reader
import qualified Data.Map.Strict as M

inline :: SSA3.Assn -> SSA3.Defs -> (SSA3.Assn, SSA3.Defs)
inline assn defs =
  let count :: (Foldable t) => t (M.Map Var Int) -> M.Map Var Int
      count      = foldl (<+>) M.empty
      assnCounts = count $ M.map (count . fmap PE.counts) assn
      defsCounts = count $ M.map PE.counts defs
      cs         = assnCounts <+> defsCounts

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

      (changed, assn', defs') = M.foldlWithKey scan (False, assn, defs) defs in
    if changed then inline assn' defs' else (assn', defs')

compile :: SSA3.Program -> Pass SSA3.Program
compile prog@(SSA3.Program decls dice assn defs) = do
  inlining <- reader inlining
  if inlining then
    let (assn', defs') = inline assn defs in
    return $ SSA3.Program decls dice assn' defs'
  else return prog
