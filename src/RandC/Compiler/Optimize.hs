module RandC.Compiler.Optimize where

import RandC.Var
import RandC.Imp
import RandC.Prob       hiding (resolve)
import RandC.Pass
import qualified RandC.Prism.Expr as PE
import RandC.Prism.Expr hiding (If, simplify)
import qualified RandC.Options as O

import Control.Monad.Reader
import qualified Data.Set        as S
import qualified Data.Map.Strict as M

assnDeps :: M.Map Var (P Expr) -> S.Set Var
assnDeps assn =
  foldl addVarDeps S.empty assn
  where addVarDeps allDeps es = foldl addExprDeps allDeps es
        addExprDeps allDeps e = S.union allDeps (vars e)

simplify :: Program -> Program
simplify (Program decls defs com) =
  Program decls (M.map PE.simplify defs) (simplifyCom com)

simplifyCom :: Com -> Com
simplifyCom (Com is) = Com $ simplifyInstrs is

simplifyInstrs :: [Instr] -> [Instr]
simplifyInstrs [] = []
simplifyInstrs (i : is) =
  case (simplifyInstr i, simplifyInstrs is) of
    (i'@(Assn assn), is') ->
      if assn == M.empty then is' else i' : is'
    (i'@(If e cThen cElse), is') ->
      if cThen == cElse then instrs cThen ++ is'
      else case e of
        Const (Bool b) -> instrs (if b then cThen else cElse) ++ is'
        _ -> i' : is'

simplifyInstr :: Instr -> Instr
simplifyInstr (Assn assns) =
  Assn (M.map (fmap PE.simplify) assns)
simplifyInstr (If e cThen cElse) =
  If (PE.simplify e) (simplifyCom cThen) (simplifyCom cElse)

maybeOptimize ::
  (O.Options -> Bool) -> (Program -> Pass Program) -> Program -> Pass Program
maybeOptimize opt f prog = do
  opt <- reader opt
  if opt then f prog else return prog

optimize :: Program -> Pass Program
optimize =
  maybeOptimize O.simplify (return . simplify)
