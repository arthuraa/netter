module Netter.Compiler where

import Netter.Pass
import qualified Netter.Imp                 as Imp
import qualified Netter.Prism               as Prism
import qualified Netter.Compiler.Optimize   as Opt
import qualified Netter.Compiler.ImpToCFG   as I2C
import qualified Netter.Compiler.CFGToUPA   as C2U
import qualified Netter.Compiler.UPAToPrism as U2P

import Control.Monad

compile :: Imp.Program -> Pass Prism.Program
compile =
  Opt.optimize >=>
  I2C.compile  >=>
  C2U.compile  >=>
  U2P.compile
