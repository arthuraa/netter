module RandC.Compiler.DToP where

import qualified RandC.D as D
import qualified RandC.P as P

import qualified Data.Map.Strict as M
import qualified Data.Set as S

addVal :: D.Valuation -> D.Die -> Int -> D.Valuation
addVal val d i d'
  | d == d' = i
  | otherwise = val d'

marginalize :: M.Map D.Die [Double] -> S.Set D.Die -> P.P D.Valuation
marginalize probs ds = foldl go (return $ const 0) $ S.toList ds
  where go distr d =
          case M.lookup d probs of
            Just dProbs -> do
              dVal <- P.P $ zip dProbs [0..]
              val  <- distr
              return $ addVal val d dVal

            Nothing ->
              error $ "DToP: Assertion failed: die " ++ show d ++ " is unbound"

undice :: M.Map D.Die [Double] -> S.Set D.Die -> D.D a -> P.P a
undice probs ds x = do
  val <- marginalize probs ds
  return $ D.resolve val x
