module RandC.Compiler where

import qualified RandC.Imp                 as Imp
import qualified RandC.Prism               as Prism
import qualified RandC.Compiler.Diceing    as I2D
import qualified RandC.Compiler.DiceToDPA  as D2DPA
import qualified RandC.Compiler.Undiceing  as DPA2UPA
import qualified RandC.Compiler.UPAToPrism as UPA2P

compile :: Imp.Program -> Prism.Program
compile =
  UPA2P.compile .
  DPA2UPA.compile .
  D2DPA.compile .
  I2D.compile
