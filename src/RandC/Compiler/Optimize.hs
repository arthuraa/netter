module RandC.Compiler.Optimize where

import RandC.Var
import RandC.Imp
import RandC.Prob       hiding (resolve)
import RandC.G          hiding (If)
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

type Deps = M.Map Var (S.Set Var)

-- Compute the dependencies of intermediate definitions on state variables
defDeps :: M.Map Var Expr -> Deps
defDeps defs = foldl updateDependencies M.empty $ M.keysSet defs
  where directDepMap = M.map vars defs
        updateDependencies deps v
          | M.member v deps =
            -- The variable v has already been visited, so we can skip it
            deps
          | otherwise =
            let directDeps = M.findWithDefault S.empty v directDepMap
                toVisit    = S.difference directDeps (M.keysSet deps)
                stateDeps  = S.difference directDeps (M.keysSet defs)
                deps'      = foldl updateDependencies deps toVisit
                allDeps    = S.unions
                             $ stateDeps
                             : [ M.findWithDefault S.empty v' deps'
                               | v' <- S.toList directDeps ] in
              M.insert v allDeps deps'

exprDep :: Deps -> Expr -> S.Set Var
exprDep deps e = S.unions [ M.findWithDefault (S.singleton v) v deps
                          | v <- S.toList $ vars e ]

probExprDep :: Deps -> P Expr -> S.Set Var
probExprDep deps e = S.unions $ fmap (exprDep deps) e

guardedExprDep :: Deps -> G (P Expr) -> S.Set Var
guardedExprDep deps e = S.unions $ fmap (probExprDep deps) e

mergeInstrs :: Deps -> [Instr] -> [Instr]
mergeInstrs deps is = go is
  where go [] = []
        go (i : is) =
          case (i, go is) of
            (i@(Assn assn), i'@(Assn assn') : is') ->
              let assnVars  = M.keysSet assn
                  assnVars' = M.keysSet assn'
                  assnDeps' = S.unions $ fmap (guardedExprDep deps) assn' in
                if S.disjoint assnVars assnDeps' &&
                   S.disjoint assnVars assnVars' then
                  Assn (M.union assn assn') : is'
                else i : i' : is'
            (i, is) -> i : is

mergeCom :: Deps -> Com -> Com
mergeCom deps (Com is) = Com $ mergeInstrs deps is

merge :: Program -> Program
merge (Program decl defs blocks) =
  Program decl defs $ mergeCom (defDeps defs) blocks

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
  Assn (M.map (fmap $ fmap PE.simplify) assns)
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
