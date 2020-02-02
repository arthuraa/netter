module RandC.ToSource where

class ToSource a where
  toSource :: a -> String
