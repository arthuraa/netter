{-# LANGUAGE DeriveFunctor #-}
module RandC.P where

import RandC.Display

import Data.List (intersperse)

data P a = P { runP :: [(Double, a)] }
  deriving (Show, Eq, Functor)

instance Applicative P where
  pure x = P [(1.0, x)]

  P fs <*> P xs = P [(pf * px, f x) | (pf, f) <- fs, (px, x) <- xs]

instance Monad P where
  return = pure

  P xs >>= f = P [(px * pres, res) | (px, x) <- xs, (pres, res) <- runP $ f x]

instance Display a => Display (P a) where
  display (P []) =
    error "Cannot have an empty choice"
  display (P [(_, x)]) =
    display x
  display (P probs) =
    concat $ intersperse " + " [show p ++ " : " ++ display x | (p, x) <- probs]
