module RandC.Compiler where

import RandC.Pass
import qualified RandC.Imp                 as Imp
import qualified RandC.Prism               as Prism
import qualified RandC.Compiler.ImpToSeq   as I2S
import qualified RandC.Compiler.SeqToCFG   as S2C
import qualified RandC.Compiler.CFGToUPA   as C2U
import qualified RandC.Compiler.UPAToPrism as U2P

import Control.Monad

compile :: Imp.Program -> Pass Prism.Program
compile =
  I2S.compile >=>
  S2C.compile >=>
  C2U.compile >=>
  U2P.compile
