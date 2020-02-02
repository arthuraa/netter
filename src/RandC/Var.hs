module RandC.Var where

import RandC.ToSource

data Var = Named String
         | Unnamed Int
  deriving (Show, Ord, Eq)

instance ToSource Var where
  toSource (Named x) = "n_" ++ x
  toSource (Unnamed n) = "u_" ++ show n
