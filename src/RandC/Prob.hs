{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
module RandC.Prob where

import Data.Text.Prettyprint.Doc
import qualified Data.Map.Strict as M
import qualified Data.Set as S

type Die = Int

data D a = Return a
         | Choice Die [D a]
  deriving (Show, Eq, Functor, Traversable, Foldable)

instance Applicative D where
  pure = Return
  Return f <*> x = fmap f x
  Choice d fs <*> x = Choice d [f <*> x | f <- fs]

instance Monad D where
  return = Return
  Return x >>= k = k x
  Choice d fs >>= k = Choice d [f >>= k | f <- fs]

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
  deriving (Show, Eq, Functor)

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
