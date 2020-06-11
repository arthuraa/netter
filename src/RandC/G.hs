{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
module RandC.G where

import qualified Data.Set as S
import Data.Text.Prettyprint.Doc
import RandC.Var
import RandC.Prism.Expr hiding (If, simplify)
import qualified RandC.Prism.Expr as PE

data G a = Return a
         | If Expr (G a) (G a)
  deriving (Show, Eq, Functor, Foldable, Traversable)

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

simplify :: Eq a => G a -> G a
simplify (Return x) = Return x
simplify (If e x y) =
  let e' = PE.simplify e
      x' = simplify x
      y' = simplify y in
    if x' == y' then x'
    else case e' of
           Const (Bool b) -> if b then x' else y'
           _ -> If e' x' y'

flatten :: G a -> [([Expr], a)]
flatten x = go [] x
  where go guards (Return x) = [(guards, x)]
        go guards (If e x y) = go (e : guards) x ++ go (UnOp Not e : guards) y

toExpr :: G PE.Expr -> PE.Expr
toExpr (Return e) = e
toExpr (If e x y) = PE.If e (toExpr x) (toExpr y)

-- | Compute the vars that appear in a guarded expression, using another
-- function aVars to find the variables that appear at the leaves.
vars :: (a -> S.Set Var) -> G a -> S.Set Var
vars aVars x = go x
  where go (Return x)   = aVars x
        go (If e x1 x2) = S.unions [PE.vars e, go x1, go x2]
