{-# LANGUAGE DeriveFunctor #-}
module RandC.G where

import RandC.Var
import qualified RandC.Prism.Expr as E

import Control.Applicative
import Data.Functor

data G a = Return a
         | If E.Expr (G a) (G a)
  deriving (Show, Eq, Functor)

instance Applicative G where
  pure = Return
  Return f <*> x = fmap f x
  If e f g <*> x = If e (f <*> x) (g <*> x)

instance Monad G where
  return = Return
  Return x >>= k = k x
  If e x1 x2 >>= k = If e (x1 >>= k) (x2 >>= k)
