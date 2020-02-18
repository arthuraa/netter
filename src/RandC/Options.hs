module RandC.Options where

data Target = Imp
            | Dice
            | SSA1
            | SSA2
            | UPA
            | Prism
  deriving (Ord, Eq)

data Options = Options { target   :: Target
                       , inlining :: Bool
                       , simplify :: Bool }
  deriving (Ord, Eq)

defaults :: Options
defaults = Options Prism True True
