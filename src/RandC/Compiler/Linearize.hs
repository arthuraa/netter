module RandC.Compiler.Linearize where

import RandC.Prism.Expr
import qualified RandC.Imp as Src
import qualified RandC.Linear as Tgt
import RandC.Options
import RandC.Pass
import qualified RandC.G as G

import qualified Data.Set        as S
import qualified Data.Map.Strict as M

compileCom :: Src.Com -> [Tgt.Block]
compileCom (Src.Com is) = compileInstrs is

compileInstrs :: [Src.Instr] -> [Tgt.Block]
compileInstrs is = concat $ map compileInstr is

mergeBlocks :: Expr -> Tgt.Block -> Tgt.Block -> Tgt.Block
mergeBlocks e bThen bElse =
  let modVars = S.union (M.keysSet bThen) (M.keysSet bElse)
      getVar b v = M.findWithDefault (return . return . Var $ v) v b in
  M.fromSet (\v -> G.If e (getVar bThen v) (getVar bElse v)) modVars

compileInstr :: Src.Instr -> [Tgt.Block]
compileInstr (Src.Assn assn) =
  [M.map return assn]
compileInstr (Src.If e cThen cElse) = merge bsThen bsElse
  where merge (bThen : bsThen) (bElse : bsElse) =
          mergeBlocks e bThen bElse : merge bsThen bsElse
        merge [] (bElse : bsElse) =
          mergeBlocks e M.empty bElse : merge [] bsElse
        merge (bThen : bsThen) [] =
          mergeBlocks e bThen M.empty : merge bsThen []
        merge [] [] = []
        bsThen = compileCom cThen
        bsElse = compileCom cElse

compile :: Src.Program -> Pass Tgt.Program
compile prog = do
  Src.Program decls defs com <- ensureTarget Linear prog
  return $ Tgt.Program decls defs $ compileCom com
