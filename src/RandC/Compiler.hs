module RandC.Compiler where

import RandC.Pass
import qualified RandC.Imp                  as Imp
import qualified RandC.Prism                as Prism
import qualified RandC.Compiler.Optimize    as Opt
import qualified RandC.Compiler.Linearize   as I2L
import qualified RandC.Compiler.Merge       as Merge
import qualified RandC.Compiler.LinearToUPA as L2U
import qualified RandC.Compiler.UPAToPrism  as U2P

import Control.Monad

compile :: Imp.Program -> Pass Prism.Program
compile =
  Opt.optimize >=>
  I2L.compile  >=>
  Merge.merge  >=>
  L2U.compile  >=>
  U2P.compile
