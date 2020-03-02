module RandC.Compiler.ImpToSeq where

import qualified RandC.Options as O
import RandC.Pass
import qualified RandC.Imp as Src
import qualified RandC.Seq as Tgt

import qualified Data.Map as M

compileCom :: Src.Com -> Tgt.Com -> Tgt.Com
compileCom Src.Skip k =
  k
compileCom (Src.Assn v e) k =
  Tgt.Assn (M.singleton v e) k
compileCom (Src.Seq c1 c2) k =
  compileCom c1 (compileCom c2 k)
compileCom (Src.If e cThen cElse) k =
  Tgt.If e (compileCom cThen Tgt.Skip) (compileCom cElse Tgt.Skip) k
compileCom (Src.Choice v ps) k =
  Tgt.Choice v ps k

compile :: Src.Program -> Pass Tgt.Program
compile prog = do
  Src.Program decls com <- ensureTarget O.Seq prog
  return $ Tgt.Program decls $ compileCom com Tgt.Skip
