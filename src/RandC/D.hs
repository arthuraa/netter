{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
module RandC.D where

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

dice :: D a -> S.Set Die
dice (Return _)    = S.empty
dice (Choice d xs) = S.insert d $ S.unions $ map dice xs

type Valuation = Die -> Int

resolve :: Valuation -> D a -> a
resolve v x = go x
  where go (Return x)    = x
        go (Choice d xs) = go $ xs !! v d
