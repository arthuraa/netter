module RandC.Compiler where

import RandC.Pass
import qualified RandC.Imp                 as Imp
import qualified RandC.Prism               as Prism
import qualified RandC.Compiler.Optimize   as Opt
import qualified RandC.Compiler.ImpToCFG   as I2C
import qualified RandC.Compiler.CFGToUPA   as C2U
import qualified RandC.Compiler.UPAToPrism as U2P

import Control.Monad

compile :: Imp.Program -> Pass Prism.Program
compile =
  Opt.optimize >=>
  I2C.compile  >=>
  C2U.compile  >=>
  U2P.compile
