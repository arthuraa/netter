{-# LANGUAGE DeriveFunctor #-}
module RandC.P where

import Data.Text.Prettyprint.Doc

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
