{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
module Netter.Prob where

import Netter.Var

import Data.Text.Prettyprint.Doc
import qualified Data.Map.Strict as M
import qualified Data.Set as S

type Die = Int

data D a = Return a
         | Choice Die [D a]
  deriving (Show, Eq, Functor, Traversable, Foldable)

reshape :: M.Map Die Int -> D a -> D a
reshape _ (Return x) =
  Return x
reshape ds (Choice d xs) =
  case M.lookup d ds of
    Just i  -> reshape ds $ xs !! i
    Nothing -> Choice d [reshape (M.insert d i ds) x
                        | (x, i) <- zip xs [0..] ]

-- Remove redundant die throws
prune :: Eq a => D a -> D a
prune (Return x)    = Return x
prune (Choice d xs) = case map prune xs of
                        [] -> error "Prob: Assertion failed: Empty choice."
                        xs'@(x : xs'') ->
                          if all (== x) xs'' then x
                          else Choice d xs'

instance Applicative D where
  pure = Return
  f <*> x = reshape M.empty $ go f x
    where go (Return f)    x = fmap f x
          go (Choice d fs) x = Choice d [go f x | f <- fs]

instance Monad D where
  return  = Return
  x >>= k = reshape M.empty $ go x
    where go (Return x)    = k x
          go (Choice d xs) = Choice d $ map go xs

instance Pretty a => Pretty (D a) where
  pretty (Return x) =
    pretty x
  pretty (Choice d xs) =
    sep [pretty "choose", pretty d, hang 0 $ pretty xs]

dice :: D a -> S.Set Die
dice (Return _)    = S.empty
dice (Choice d xs) = S.insert d $ S.unions $ map dice xs

type Valuation = Die -> Int

resolve :: Valuation -> D a -> a
resolve v x = go x
  where go (Return x)    = x
        go (Choice d xs) = go $ xs !! v d

data P a = P { runP :: [(Double, a)] }
  deriving (Show, Eq, Functor, Traversable, Foldable)

ofP :: P a -> Maybe a
ofP (P [(_, x)]) = Just x
ofP _            = Nothing

instance Applicative P where
  pure x = P [(1.0, x)]

  P fs <*> P xs = P [(pf * px, f x) | (pf, f) <- fs, (px, x) <- xs]

instance Monad P where
  return = pure

  P xs >>= f = P [(px * pres, res) | (px, x) <- xs, (pres, res) <- runP $ f x]

instance Pretty a => Pretty (P a) where
  pretty (P []) =
    error "Cannot have an empty choice"
  pretty (P [(_, x)]) =
    pretty x
  pretty (P probs) =
    cat $ punctuate (pretty " + ") [ pretty p <> pretty " : " <> pretty x
                                   | (p, x) <- probs ]

instance HasVars a => HasVars (P a) where
  vars p = S.unions $ fmap vars p

addVal :: Valuation -> Die -> Int -> Valuation
addVal val d i d'
  | d == d' = i
  | otherwise = val d'

marginalize :: M.Map Die [Double] -> S.Set Die -> P Valuation
marginalize probs ds = foldl go (return $ const 0) $ S.toList ds
  where go distr d =
          case M.lookup d probs of
            Just dProbs -> do
              dVal <- P $ zip dProbs [0..]
              val  <- distr
              return $ addVal val d dVal

            Nothing ->
              error $ "Prob: Assertion failed: die " ++ show d ++ " is unbound"

undice :: M.Map Die [Double] -> S.Set Die -> D a -> P a
undice probs ds x = do
  val <- marginalize probs ds
  return $ resolve val x
