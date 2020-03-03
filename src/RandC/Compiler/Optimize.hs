module RandC.Compiler.Optimize where

import RandC.Var
import RandC.Imp
import RandC.Prob
import RandC.Pass
import RandC.Prism.Expr hiding (If)

import qualified Data.Set as S
import qualified Data.Map as M

assnDeps :: M.Map Var (P Expr) -> S.Set Var
assnDeps assn =
  foldl addVarDeps S.empty assn
  where addVarDeps allDeps es = foldl addExprDeps allDeps es
        addExprDeps allDeps e = S.union allDeps (vars e)

mergeAssnsCom :: Com -> Com
mergeAssnsCom c = Com $ mergeAssnsInstrs $ instrs c

mergeAssnsInstrs :: [Instr] -> [Instr]
mergeAssnsInstrs [] = []
mergeAssnsInstrs (If e c1 c2 : is) =
  If e (mergeAssnsCom c1) (mergeAssnsCom c2) : mergeAssnsInstrs is
mergeAssnsInstrs (i@(Assn assns) : is) =
  case mergeAssnsInstrs is of
    i'@(Assn assns') : is' ->
      if S.disjoint (M.keysSet assns) (assnDeps assns') then
        Assn (M.unionWith (\_ es -> es) assns assns') : is'
      else i : i' : is
    is' -> i : is'

mergeAssns :: Program -> Program
mergeAssns (Program decls com) = Program decls (mergeAssnsCom com)

optimize :: Program -> Pass Program
optimize prog = return $ mergeAssns prog
