module RandC.Compiler.Optimize where

import RandC.Var
import RandC.Dependencies
import RandC.Imp
import RandC.Prob       hiding (resolve)
import qualified RandC.G as G
import RandC.G          hiding (If, simplify)
import RandC.Pass
import qualified RandC.Prism.Expr as PE
import RandC.Prism.Expr hiding (If, simplify)
import qualified RandC.Options as O

import Control.Monad.Reader
import qualified Data.Set        as S
import qualified Data.Map.Strict as M

-- * Minimizing the control-flow graph

-- | The most important optimization when converting from Imp to CFG is to
-- collapse successive assignments, which allows us to use fewer blocks in the
-- CFG, and thus fewer PC values in the Prism code.  Two consecutive assignments
-- @assn1@ and @assn2@ can be merged when
--
--     1. the expressions in @assn2@ do not use variables assigned by @assn1@, and
--
--     2. @assn1@ and @assn2@ assign to disjoint sets of variables.
--
-- This computation is done in the "Dependencies" module.

-- | When an if statement has only two blocks of assignments, one in each
-- branch, we can combine the two branches using a conditional expression.
condAssn :: Expr -> M.Map Var (G (P Expr)) -> M.Map Var (G (P Expr)) -> M.Map Var (G (P Expr))
condAssn e assn1 assn2 =
  let modVars       = S.union (M.keysSet assn1) (M.keysSet assn2)
      varVal assn v = M.findWithDefault (return $ return $ Var v) v assn in
    M.fromSet (\v -> G.If e (varVal assn1 v) (varVal assn2 v)) modVars

mergeInstr :: StateDeps -> Instr -> Instr
mergeInstr _ (Assn assn) =
  Assn assn
mergeInstr deps (If e c1 c2) =
  let c1' = mergeCom deps c1
      c2' = mergeCom deps c2 in
    case (instrs c1', instrs c2') of
      ([], []) ->
        Assn M.empty
      ([Assn assn1], []) ->
        Assn (condAssn e assn1 M.empty)
      ([], [Assn assn2]) ->
        Assn (condAssn e M.empty assn2)
      ([Assn assn1], [Assn assn2]) ->
        Assn (condAssn e assn1 assn2)
      (_, _) -> If e c1' c2'

mergeInstrs :: StateDeps -> [Instr] -> [Instr]
mergeInstrs deps is = go is
  where go [] = []
        go (i : is) =
          case (mergeInstr deps i, go is) of
            (i@(Assn assn), i'@(Assn assn') : is') ->
              let assnVars  = M.keysSet assn
                  assnVars' = M.keysSet assn'
                  assnDeps' = S.unions $ fmap (guardedExprStateDeps deps) assn' in
                if S.disjoint assnVars assnDeps' &&
                   S.disjoint assnVars assnVars' then
                  Assn (M.union assn assn') : is'
                else i : i' : is'
            (i, is) -> i : is

mergeCom :: StateDeps -> Com -> Com
mergeCom deps (Com is) = Com $ mergeInstrs deps is

merge :: Program -> Program
merge (Program decl defs rews blocks) =
  Program decl defs rews $ mergeCom (definitionStateDeps defs) blocks

simplify :: Program -> Program
simplify (Program decls defs rews com) =
  Program decls (M.map PE.simplify defs) (M.map PE.simplify rews) (simplifyCom com)

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
  Assn (M.map (G.simplify . fmap (fmap PE.simplify)) assns)
simplifyInstr (If e cThen cElse) =
  If (PE.simplify e) (simplifyCom cThen) (simplifyCom cElse)

maybeOptimize ::
  (O.Options -> Bool) -> (Program -> Pass Program) -> Program -> Pass Program
maybeOptimize opt f prog = do
  opt <- reader opt
  if opt then f prog else return prog

optimize :: Program -> Pass Program
optimize =
  maybeOptimize O.merge (return . merge) >=>
  maybeOptimize O.simplify (return . simplify)
