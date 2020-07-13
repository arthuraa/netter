{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

module RandC.Compiler.Optimize where

import RandC.Var
import RandC.Imp
import RandC.Prob       hiding (resolve)
import qualified RandC.G as G
import RandC.G          hiding (If, simplify)
import RandC.Pass
import qualified RandC.Prism.Expr as PE
import RandC.Prism.Expr hiding (If, simplify)
import qualified RandC.Options as O
import qualified RandC.FFun as F


import Control.Monad.State
import Control.Monad.Reader
import Data.Set (Set)
import qualified Data.Set        as S
import qualified Data.Map.Strict as M
import Data.Map.Strict (Map)

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

mergeInstr :: Locals -> Instr -> Instr
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
mergeInstr deps (Block vs c) = Block vs (mergeCom deps c)

mergeInstrs :: Locals -> [Instr] -> [Instr]
mergeInstrs deps is = go is
  where go [] = []
        go (i : is) =
          case (mergeInstr deps i, go is) of
            (i@(Assn assn), i'@(Assn assn') : is') ->
              let assnVars  = M.keysSet assn
                  assnVars' = M.keysSet assn'
                  assnDeps' = S.unions $ fmap (stateDeps deps) assn' in
                if S.disjoint assnVars assnDeps' &&
                   S.disjoint assnVars assnVars' then
                  Assn (M.union assn assn') : is'
                else i : i' : is'
            (i, is) -> i : is

mergeCom :: Locals -> Com -> Com
mergeCom deps (Com is) = Com $ mergeInstrs deps is

merge :: Program -> Program
merge (Program decl defs rews blocks) =
  Program decl defs rews $ mergeCom defs blocks

simplify :: Program -> Program
simplify (Program decls defs rews com) =
  let simplifyLocals (e, deps) = (PE.simplify e, deps) in
  Program decls (M.map simplifyLocals defs) (M.map PE.simplify rews) (simplifyCom com)

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
    (i'@(Block vs c), is') ->
      if S.null vs then instrs c ++ is' else i' : is'

simplifyInstr :: Instr -> Instr
simplifyInstr (Assn assns) =
  Assn (M.map (G.simplify . fmap (fmap PE.simplify)) assns)
simplifyInstr (If e cThen cElse) =
  If (PE.simplify e) (simplifyCom cThen) (simplifyCom cElse)
simplifyInstr (Block vs c) = Block vs (simplifyCom c)

type I a = StateT Locals Pass a

substAssn :: Renaming -> Map Var (G (P Expr)) -> Map Var (G (P Expr))
substAssn sigma assn = (fmap.fmap.fmap) (subst (PE.Var . (sigma F.!))) assn

conflicts :: Locals -> Renaming -> Set Var -> Set Var
conflicts locals sigma vs = loop (length $ F.supp sigma) sigma vs (F.supp sigma S.\\ vs) vs
  where loop k sigma acc rem next =
          if k > 0 then
            let hasConflict v = not (S.disjoint (stateDeps locals (sigma F.! v)) next)
                next' = S.filter hasConflict rem in
              if next' == S.empty then acc
              else loop (k - 1) sigma (S.union acc next') (rem S.\\ next') next'
          else acc

intern :: Map Var (G Expr) -> I Renaming
intern assn =
  let assn' = fmap toExpr assn
      intern1 v e = do
        v' <- fresh (name v)
        modify $ \locals -> insertLocals v' e locals
        return v' in
    mkrenaming <$> M.traverseWithKey intern1 assn'

inlineLoop :: Renaming -> [Instr] -> I (Renaming, [Instr])
inlineLoop sigma [] = return (sigma, [])

inlineLoop sigma (Assn assn : c) = do
  ls <- get
  let assn' = substAssn sigma assn
  let detAssn = M.mapMaybe (traverse ofP) assn'
  detAssn' <- intern detAssn
  let cs = conflicts ls sigma (M.keysSet assn')
  let sigma_def v
        | S.member v cs = v
        | S.member v (F.supp detAssn') = detAssn' F.! v
        | otherwise = sigma F.! v
  let sigma' = mkrenaming
               $ M.fromList [(v, sigma_def v)
                            | v <- S.toList (S.union (F.supp detAssn') (F.supp sigma))]
  (sigma'', c') <- inlineLoop sigma' c
  return (sigma'', Assn assn' : c')

inlineLoop sigma (If e cthen celse : c) = do
  locals <- get
  let e' = subst (PE.Var . (sigma F.!)) e
  (sigma_then, cthen') <- inlineLoop sigma (instrs cthen)
  (sigma_else, celse') <- inlineLoop sigma (instrs celse)
  let modified = S.union (modVars (Com cthen')) (modVars (Com celse'))
  let canMerge = S.disjoint (stateDeps locals e') modified
  let sigma_def v
        | canMerge = PE.If e' (PE.Var (sigma_then F.! v)) (PE.Var (sigma_else F.! v))
        | sigma_then F.! v == sigma_else F.! v = PE.Var $ sigma_then F.! v
        | otherwise = PE.Var v
  let sigma' = M.fromList [(v, sigma_def v)
                         | v <- S.toList $ S.union (F.supp sigma_then) (F.supp sigma_else) ]
  sigma'' <- intern $ fmap return sigma'
  (sigma''', c') <- inlineLoop sigma'' c
  return (sigma''', If e' (Com cthen') (Com celse') : c')

inlineLoop sigma (Block vs block : c) = do
  locals <- get
  let cs = conflicts locals sigma vs
  let sigma_def' v
        | S.member v cs = v
        | otherwise = sigma F.! v
  let sigma' = mkrenaming $ M.fromList [(v, sigma_def' v) | v <- S.toList $ F.supp sigma]
  (sigma'', block') <- inlineLoop sigma' (instrs block)
  let cs' = conflicts locals sigma'' vs
  let sigma_def''' v
        | S.member v cs' = v
        | otherwise = sigma'' F.! v
  let sigma''' = mkrenaming $ M.fromList [(v, sigma_def''' v) | v <- S.toList $ F.supp sigma'']
  (sigma'''', c') <- inlineLoop sigma''' c
  return (sigma'''', Block vs (Com block') : c')

inline :: Program -> Pass Program
inline Program{..} =
  if M.null pDefs then do
    ((sigma, pCom'), pDefs') <- runStateT (inlineLoop (mkrenaming M.empty) (instrs pCom)) M.empty
    let pRewards' = fmap (subst (Var . (sigma F.!))) pRewards
    return Program{pDefs = pDefs', pRewards = pRewards', pCom = Com pCom', ..}
  else error "Inlining does not work with local definitions"

substG :: Monad m => (Var -> m Expr) -> G (P Expr) -> m (G (P Expr))
substG f x = go x
  where go (G.Return x) = G.Return <$> traverse (substM f) x
        go (G.If e x y) = G.If <$> substM f e <*> go x <*> go y

class NeedsVar a where
  needsVar :: Locals -> Set Var -> a -> Set Var

instance NeedsVar Com where
  needsVar depMap vs (Com is) =
    foldr (\i vs -> needsVar depMap vs i) vs is

instance NeedsVar Instr where
  needsVar depMap vs (Assn assn) =
    let assn' = M.filterWithKey (\v _ -> v `S.member` vs) assn in
      S.union vs (S.unions $ fmap (stateDeps depMap) assn')
  needsVar depMap vs (If e cThen cElse) =
    let vsThen = needsVar depMap vs cThen
        vsElse = needsVar depMap vs cElse in
      S.unions [stateDeps depMap e, vsThen, vsElse]
  needsVar depMap vs (Block _ c) = needsVar depMap vs c

class FilterVars a where
  filterVars :: Set Var -> a -> a

instance FilterVars Com where
  filterVars vs (Com is) = Com [filterVars vs i | i <- is]

instance FilterVars Instr where
  filterVars vs (Assn assn) =
    Assn $ M.filterWithKey (\v _ -> v `S.member` vs) assn
  filterVars vs (If e cThen cElse) = If e (filterVars vs cThen) (filterVars vs cElse)
  filterVars vs (Block vs' c) = Block (S.intersection vs vs') (filterVars vs c)

trim :: Program -> Program
trim Program{..} =
  let keep0      = S.unions $ fmap (stateDeps pDefs) pRewards
      keep1      = needsVar pDefs keep0 pCom
      pVarDecls' = M.filterWithKey (\v _ -> v `S.member` keep1) pVarDecls
      pDefs'     = M.filter (\(_, deps) -> deps `S.isSubsetOf` keep1) pDefs
      pCom'      = filterVars keep1 pCom in
    Program pVarDecls' pDefs' pRewards pCom'

maybeOptimize ::
  (O.Options -> Bool) -> (Program -> Pass Program) -> Program -> Pass Program
maybeOptimize opt f prog = do
  opt <- reader opt
  if opt then f prog else return prog

optimize :: Program -> Pass Program
optimize =
  maybeOptimize O.merge    (return . merge)    >=>
  maybeOptimize O.simplify (return . simplify) >=>
  maybeOptimize O.inlining inline              >=>
  maybeOptimize O.trimming (return . trim)
