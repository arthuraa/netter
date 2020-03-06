{-# LANGUAGE DeriveDataTypeable #-}
module RandC.Options where

import System.Console.CmdArgs.Implicit

data Target = Imp
            | Linear
            | UPA
            | Prism
  deriving (Ord, Eq, Read, Show, Data, Typeable)

data Options = Options { target   :: Target
                       , inlining :: Bool
                       , merge    :: Bool
                       , simplify :: Bool }
  deriving (Ord, Eq, Show, Data, Typeable)

readOptions :: IO Options
readOptions =
  cmdArgs $ Options { target   = Prism &= help "Output format"
                    , inlining = True  &= help "Perform inlining"
                    , merge    = True  &= help "Perform assignments in parallel when possible"
                    , simplify = True  &= help "Perform simplifications" }
          &= program "randc"
          &= summary "randc v0.1"
