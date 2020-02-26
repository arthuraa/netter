{-# LANGUAGE DeriveDataTypeable #-}
module RandC.Options where

import System.Console.CmdArgs.Implicit

data Target = Imp
            | Dice
            | SSA1
            | SSA2
            | UPA
            | Prism
  deriving (Ord, Eq, Read, Show, Data, Typeable)

data Options = Options { target   :: Target
                       , inlining :: Bool
                       , simplify :: Bool }
  deriving (Ord, Eq, Show, Data, Typeable)

readOptions :: IO Options
readOptions =
  cmdArgs Options { target   = Prism &= help "Output format"
                  , inlining = True  &= help "Perform inlining"
                  , simplify = True  &= help "Perform simplifications" }
