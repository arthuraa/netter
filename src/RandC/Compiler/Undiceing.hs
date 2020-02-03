module RandC.Compiler.Undiceing where

import RandC.Var
import RandC.P
import RandC.Dice.Expr (Die, at)
import qualified RandC.Dice.Expr  as DE
import qualified RandC.Prism.Expr as PE

import qualified Data.Map as M
import qualified Data.Set as S

type Valuation = Die -> Int

addVal :: Valuation -> Die -> Int -> Valuation
addVal val d i d'
  | d == d' = i
  | otherwise = val d'

-- Convert an expression with dice into a deterministic expression given a
-- valuation val for the die values.
compileExpr :: Valuation -> DE.Expr -> PE.Expr
compileExpr val e = go e
  where go (DE.Var v)            = PE.Var v
        go (DE.Const c)          = PE.Const c
        go (DE.UnOp o e)         = PE.UnOp o $ go e
        go (DE.BinOp o e1 e2)    = PE.BinOp o (go e1) (go e2)
        go (DE.If e eThen eElse) = PE.If (go e) (go eThen) (go eElse)
        go (DE.Choice d es)      = go $ es !! val d

marginalize :: M.Map Die [Double] -> S.Set Die -> P Valuation
marginalize probs ds = foldl go (return $ const 0) $ S.toList ds
  where go distr d =
          case M.lookup d probs of
            Just dProbs -> do
              dVal <- P $ zip dProbs [0..]
              val  <- distr
              return $ addVal val d dVal

            Nothing ->
              error $ "Assertion failed: die " ++ show d ++ " is unbound"

type DepClass = (S.Set Var, S.Set Die)

dependencies :: M.Map Var (S.Set Die) -> [DepClass]
dependencies = M.foldrWithKey (\v ds -> addDeps (S.singleton v, ds)) []
  where addDeps (vs, ds) [] = [(vs, ds)]
        addDeps (vs, ds) ((vs', ds') : rest)
          | S.disjoint ds ds' =
            (vs', ds') : addDeps (vs, ds) rest
          | otherwise =
            addDeps (vs `S.union` vs', ds `S.union` ds') rest

compileDepClass ::
  M.Map Die [Double] -> DepClass -> M.Map Var DE.Expr -> P (M.Map Var PE.Expr)
compileDepClass probs (vs, ds) m = do
  val <- marginalize probs ds
  return $ M.fromSet (\v -> compileExpr val $ m `at` v) vs

compile ::
  M.Map Die [Double] -> M.Map Var DE.Expr -> [(S.Set Var, P (M.Map Var PE.Expr))]
compile probs es =
  let dcs = dependencies $ M.map DE.dice es in
    [(vs, compileDepClass probs dc es) | dc@(vs, _) <- dcs]
