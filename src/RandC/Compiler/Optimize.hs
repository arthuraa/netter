{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

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

import Control.Lens hiding (Const)
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
mergeInstr deps (Block vs c) = Block vs (mergeCom deps c)

mergeInstrs :: StateDeps -> [Instr] -> [Instr]
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
    (i'@(Block vs c), is') ->
      if S.null vs then instrs c ++ is' else i' : is'

simplifyInstr :: Instr -> Instr
simplifyInstr (Assn assns) =
  Assn (M.map (G.simplify . fmap (fmap PE.simplify)) assns)
simplifyInstr (If e cThen cElse) =
  If (PE.simplify e) (simplifyCom cThen) (simplifyCom cElse)
simplifyInstr (Block vs c) = Block vs (simplifyCom c)

data IS = IS { _locals   :: Map Var Expr
             , _renaming :: Map Var Var }
  deriving (Eq, Ord, Show)

makeLenses ''IS

type I a = StateT IS Pass a

inline :: Program -> Pass Program
inline Program{..} =
  if M.null pDefs then do
    (pCom', IS pDefs' ren) <- runStateT (inlineCom pCom) (IS M.empty M.empty)
    let pRewards' = fmap (subst (Var . rename ren)) pRewards
    return Program{pDefs = pDefs', pRewards = pRewards', pCom = pCom', ..}
  else error "Inlining does not work with local definitions"

inlineCom :: Com -> I Com
inlineCom (Com is) = Com <$> inlineInstrs is

inlineInstrs :: [Instr] -> I [Instr]
inlineInstrs [] = return []
inlineInstrs (i : is) = do
  is1 <- inlineInstr  i
  is2 <- inlineInstrs is
  return $ is1 ++ is2

substG :: Monad m => (Var -> m Expr) -> G (P Expr) -> m (G (P Expr))
substG f x = go x
  where go (G.Return x) = G.Return <$> traverse (substM f) x
        go (G.If e x y) = G.If <$> substM f e <*> go x <*> go y

inlineInstr :: Instr -> I [Instr]
inlineInstr (Assn assn) = do
  ren   <- use renaming
  renaming .= M.empty
  assn' <- flip M.traverseMaybeWithKey assn $ \lhs rhs -> do
    -- Check if the right-hand side is deterministic
    case traversed ofP rhs of
      Just rhs -> do
        -- If so, turn the binding into a formula
        lhs' <- fresh $ name lhs
        let rhs' = subst (Var . rename ren) (toExpr rhs)
        locals  .at lhs' ?= rhs'
        renaming.at lhs  ?= lhs'
        return Nothing
      Nothing -> do
        -- Otherwise, just rename the formula
        Just <$> substG (return . Var . rename ren) rhs

  ren' <- use renaming
  renaming .= (ren' `M.union` ren) `M.withoutKeys` (M.keysSet assn')
  if M.null assn' then return [] else return [Assn assn']

inlineInstr (If e cThen cElse) = do
  ren0     <- use renaming
  cThen'   <- inlineCom cThen
  renThen  <- use renaming
  renaming .= ren0
  cElse'   <- inlineCom cElse
  renElse  <- use renaming
  renaming .= ren0
  if cThen' == skip && cElse' == skip then do
    let merge v = PE.If e (Var $ rename renThen v) (Var $ rename renElse v)
    let renamed = M.keysSet renThen `S.union` M.keysSet renElse
    inlineInstr $ Assn $ M.fromSet (return . return . merge) renamed
  else do
    let flushVars c ren = cat c $ Com [Assn $ M.map (return . return . Var) ren]
    let e' = subst (Var . rename ren0) e
    return [If e' (flushVars cThen' renThen) (flushVars cElse' renElse)]

inlineInstr (Block vs c) = do
  c' <- inlineCom c
  if S.null vs then return $ instrs c'
  else return [Block vs c']

class NeedsVar a where
  needsVar :: StateDeps -> Set Var -> a -> Set Var

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
  let depMap     = definitionStateDeps pDefs
      keep0      = S.unions $ fmap (stateDeps depMap) pRewards
      keep1      = needsVar depMap keep0 pCom
      pVarDecls' = M.filterWithKey (\v _ -> v `S.member` keep1) pVarDecls
      pDefs'     = M.filter (\e -> stateDeps depMap e `S.isSubsetOf` keep1) pDefs
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
