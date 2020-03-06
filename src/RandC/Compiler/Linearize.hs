module RandC.Compiler.Linearize where

import RandC.Prism.Expr
import qualified RandC.Imp as Src
import qualified RandC.Linear as Tgt
import RandC.Options
import RandC.Pass

import qualified Data.Map.Strict as M

compileCom :: [Expr] -> Src.Com -> [Tgt.Block]
compileCom guards (Src.Com is) = compileInstrs guards is

compileInstrs :: [Expr] -> [Src.Instr] -> [Tgt.Block]
compileInstrs guards is = concat $ map (compileInstr guards) is

compileInstr :: [Expr] -> Src.Instr -> [Tgt.Block]
compileInstr guards (Src.Assn assn) =
  [M.map (\es -> [(guards, es)]) assn]
compileInstr guards (Src.If e cThen cElse) = merge bsThen bsElse
  where merge (bThen : bsThen) (bElse : bsElse) =
          M.union bThen bElse : merge bsThen bsElse
        merge [] bsElse = bsElse
        merge bsThen [] = bsThen
        bsThen = compileCom (e : guards) cThen
        bsElse = compileCom (UnOp Not e : guards) cElse

compile :: Src.Program -> Pass Tgt.Program
compile prog = do
  Src.Program decls defs com <- ensureTarget Linear prog
  return $ Tgt.Program decls defs $ compileCom [] com
