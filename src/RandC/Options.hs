module RandC.Options where

data Target = Imp
            | Dice
            | SSA1
            | SSA2
            | SSA3
            | UPA
            | Prism
  deriving (Ord, Eq)

data Options = Options { target   :: Target
                       , inlining :: Bool }
  deriving (Ord, Eq)

defaults :: Options
defaults = Options Prism True
