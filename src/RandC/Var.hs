module RandC.Var where

import RandC.ToSource

data Var = Named String
         | Unnamed String Int
  deriving (Show, Ord, Eq)

instance ToSource Var where
  toSource (Named x) = "n_" ++ x
  toSource (Unnamed x n) = "u_" ++ x ++ "_" ++ show n
