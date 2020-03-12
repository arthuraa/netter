{-# LANGUAGE DeriveFunctor #-}
module RandC.G where

import Data.Text.Prettyprint.Doc
import RandC.Prism.Expr hiding (If)

data G a = Return a
         | If Expr (G a) (G a)
  deriving (Show, Eq, Functor)

instance Applicative G where
  pure = Return
  Return f <*> x = fmap f x
  If e f g <*> x = If e (f <*> x) (g <*> x)

instance Monad G where
  return = Return
  Return x >>= k = k x
  If e x1 x2 >>= k = If e (x1 >>= k) (x2 >>= k)

instance Pretty a => Pretty (G a) where
  pretty (Return x) =
    pretty x
  pretty (If e x y) =
    sep [ pretty e, pretty "?", parens (pretty x), pretty ":", parens (pretty y) ]

flatten :: G a -> [(Expr, a)]
flatten x = go [] x
  where go guards (Return x) = [(conj guards, x)]
        go guards (If e x y) = go (e : guards) x ++ go (UnOp Not e : guards) y
