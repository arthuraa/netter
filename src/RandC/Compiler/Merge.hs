module RandC.Compiler.Merge where

import RandC.Var
import RandC.Prob
import RandC.Linear
import RandC.G
import RandC.Prism.Expr
import qualified RandC.Options as O
import RandC.Pass

import Control.Monad.Reader
import qualified Data.Map.Strict as M
import qualified Data.Set        as S

type Deps = M.Map Var (S.Set Var)

-- Compute the dependencies of intermediate definitions on state variables
defDeps :: M.Map Var Expr -> Deps
defDeps defs = foldl updateDependencies M.empty $ M.keysSet defs
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

exprDep :: Deps -> Expr -> S.Set Var
exprDep deps e = S.unions [ M.findWithDefault (S.singleton v) v deps
                          | v <- S.toList $ vars e ]

probExprDep :: Deps -> P Expr -> S.Set Var
probExprDep deps e = S.unions $ fmap (exprDep deps) e

guardedExprDep :: Deps -> G (P Expr) -> S.Set Var
guardedExprDep deps e = S.unions $ fmap (probExprDep deps) e

mergeBlocks :: Deps -> [Block] -> [Block]
mergeBlocks deps blocks = go blocks
  where go [] = []
        go (block : blocks) =
          case go blocks of
            [] ->
              block : blocks
            block' : blocks' ->
              let blockVars  = M.keysSet block
                  blockVars' = M.keysSet block'
                  blockDeps  = S.unions $ fmap (guardedExprDep deps) block
                  blockDeps' = S.unions $ fmap (guardedExprDep deps) block' in
                if S.disjoint blockVars  blockDeps' &&
                   S.disjoint blockVars' blockDeps  &&
                   S.disjoint blockVars  blockVars' then
                  M.union block block' : blocks'
                else block : blocks

merge :: Program -> Pass Program
merge prog@(Program decl defs blocks) = do
  doMerge <- reader O.merge
  if doMerge then
    return $ Program decl defs $ mergeBlocks (defDeps defs) blocks
  else return prog
