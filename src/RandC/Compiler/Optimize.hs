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
import RandC.FFun (FFun)
import qualified RandC.FFun as F

import Control.Monad.Identity
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

substGM :: Monad m => (Var -> m Expr) -> G (P Expr) -> m (G (P Expr))
substGM f x = go x
  where go (G.Return x) = G.Return <$> traverse (substM f) x
        go (G.If e x y) = G.If <$> substM f e <*> go x <*> go y

substG :: (Var -> Expr) -> G (P Expr) -> G (P Expr)
substG f = runIdentity . substGM (Identity . f)

substAssn :: Renaming -> Map Var (G (P Expr)) -> Map Var (G (P Expr))
substAssn sigma assn = fmap (substG (PE.Var . (sigma F.!))) assn

conflicts :: Renaming -> Set Var -> I (Set Var)
conflicts sigma vs = do
  locals <- get
  loop locals (S.size $ F.supp sigma) sigma vs (F.supp sigma S.\\ vs) vs
  where loop locals k sigma acc rem next =
          if k > 0 then
            let hasConflict v = not (S.disjoint (stateDeps locals (sigma F.! v)) next)
                next' = S.filter hasConflict rem in
              if next' == S.empty then return acc
              else loop locals (k - 1) sigma (S.union acc next') (rem S.\\ next') next'
          else return acc

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
  let assn' = substAssn sigma assn
  let detAssn = M.mapMaybe (traverse ofP) assn'
  detAssn' <- intern detAssn
  cs <- conflicts sigma (M.keysSet assn')
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
  cs <- conflicts sigma vs
  let sigma_def' v
        | S.member v cs = v
        | otherwise = sigma F.! v
  let sigma' = mkrenaming $ M.fromList [(v, sigma_def' v) | v <- S.toList $ F.supp sigma]
  (sigma'', block') <- inlineLoop sigma' (instrs block)
  cs' <- conflicts sigma'' vs
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

type Dependencies = FFun Var (Set Var)

mkdeps :: Map Var (Set Var) -> Dependencies
mkdeps = F.mkffun S.singleton

liftDeps :: Dependencies -> Set Var -> Set Var
liftDeps deps vs = S.unions [deps F.! v | v <- S.toList vs]

depsComp :: Dependencies -> Dependencies -> Dependencies
depsComp deps deps' =
  mkdeps $ M.fromList [(v, liftDeps deps (deps' F.! v))
                      | v <- S.toList (S.union (F.supp deps) (F.supp deps'))]

assnDeps :: Locals -> Map Var (G (P Expr)) -> Dependencies
assnDeps defs assn =
  let def v
        | Just gp <- M.lookup v assn = stateDeps defs gp
        | otherwise = S.singleton v in
    mkdeps $ M.fromList [(v, def v) | v <- M.keys assn]

ifDeps :: Locals -> Expr -> Dependencies -> Dependencies -> Set Var -> Dependencies
ifDeps defs e deps_then deps_else mod =
  let ve = stateDeps defs e in
    mkdeps $ M.fromList [(v, S.unions [ve, deps_then F.! v, deps_else F.! v]) | v <- S.toList mod]

blockDeps :: Set Var -> Dependencies -> Dependencies
blockDeps locals db =
  let deps_locals = mkdeps $ M.fromList [(v, S.empty) | v <- S.toList locals]
      deps_block = depsComp deps_locals db in
    mkdeps $ M.fromList [(v, deps_block F.! v) | v <- S.toList (F.supp deps_block)
                                               , not (S.member v locals)]


liveVarsLoop :: Int -> Dependencies -> Set Var -> Set Var
liveVarsLoop k deps vs =
  if k > 0 then
    let next = liftDeps deps vs in
      if S.isSubsetOf next vs then vs else liveVarsLoop (k - 1) deps (S.union vs next)
  else vs

data MCom a = MSkip
            | MAssn (Map Var (G (P Expr))) (MCom a) a
            | MIf Expr (MCom a) a (MCom a) a (MCom a) a
            | MBlock (Set Var) (MCom a) a (MCom a) a

deadStoreElimOptInit :: Locals -> [Instr] -> (MCom Dependencies, Dependencies, Set Var)
deadStoreElimOptInit _ [] = (MSkip, mkdeps M.empty, S.empty)
deadStoreElimOptInit defs (Assn assn : c) =
  let (mc, deps_c, mod_c) = deadStoreElimOptInit defs c in
    (MAssn assn mc deps_c,
     depsComp (assnDeps defs assn) deps_c,
     S.union (M.keysSet assn) mod_c)

deadStoreElimOptInit defs (If e cthen celse : c) =
  let (mcthen, deps_then, mod_then) = deadStoreElimOptInit defs (instrs cthen)
      (mcelse, deps_else, mod_else) = deadStoreElimOptInit defs (instrs celse)
      (mc, deps_c, mod_c) = deadStoreElimOptInit defs c
      deps_b = ifDeps defs e deps_then deps_else (S.union mod_then mod_else) in
    (MIf e mcthen deps_then mcelse deps_else mc deps_c,
     depsComp deps_b deps_c,
     S.unions [mod_then, mod_else, mod_c])

deadStoreElimOptInit defs (Block locals block : c) =
  let (mblock, deps_block, mod_block) = deadStoreElimOptInit defs (instrs block)
      (mc, deps_c, mod_c) = deadStoreElimOptInit defs c in
    (MBlock locals mblock deps_block mc deps_c,
     depsComp (blockDeps locals deps_block) deps_c,
     (mod_block S.\\ locals) `S.union` mod_c)

deadStoreElimOptLoop :: MCom Dependencies -> Set Var -> [Instr]
deadStoreElimOptLoop MSkip _ = []
deadStoreElimOptLoop (MAssn assn mc deps_c) live =
  let live' = liftDeps deps_c live
      assn' = M.filterWithKey (\v _ -> v `S.member` live') assn
      c'    = deadStoreElimOptLoop mc live in
    Assn assn' : c'
deadStoreElimOptLoop (MIf e mcthen _ mcelse _ mc deps_c) live =
  let live' = liftDeps deps_c live
      cthen' = deadStoreElimOptLoop mcthen live'
      celse' = deadStoreElimOptLoop mcelse live'
      c' = deadStoreElimOptLoop mc live in
    If e (Com cthen') (Com celse') : c'
deadStoreElimOptLoop (MBlock locals mblock _ mc deps_c) live =
  let live' = liftDeps deps_c live
      live'' = live' S.\\ locals
      block' = deadStoreElimOptLoop mblock live''
      c' = deadStoreElimOptLoop mc live in
    Block locals (Com block') : c'

deadStoreElimOpt :: Locals -> Com -> Set Var -> (Com, Set Var)
deadStoreElimOpt defs c vs0 =
  let (mc, deps_c, _) = deadStoreElimOptInit defs (instrs c)
      vs = vs0 `S.union` liftDeps deps_c (F.supp deps_c)
      live = liveVarsLoop (S.size vs) deps_c vs0 in
    (Com $ deadStoreElimOptLoop mc live, live)

comUsedVars :: Locals -> Com -> Set Var
comUsedVars locals = doCom
  where doCom c = S.unions [doInstr i | i <- instrs c]
        doInstr (Assn assn) =
          S.union (M.keysSet assn)
          (S.unions [stateDeps locals gpe | gpe <- M.elems assn])
        doInstr (If e cthen celse) =
          S.unions [stateDeps locals e, doCom cthen, doCom celse]
        doInstr (Block vs block) = S.union vs (doCom block)

trim :: Program -> Program
trim Program{..} =
  let keep0 = S.unions $ fmap (stateDeps pDefs) pRewards
      (pCom', _) = deadStoreElimOpt pDefs pCom keep0
      usedVars = comUsedVars pDefs pCom'
      pDefs' = M.filter (\(_, deps) -> deps `S.isSubsetOf` usedVars) pDefs
      pVarDecls' = M.filterWithKey (\v _ -> v `S.member` usedVars) pVarDecls in
    Program{pVarDecls = pVarDecls', pCom = pCom', pDefs = pDefs', ..}

maybeOptimize ::
  (O.Options -> Bool) -> (Program -> Pass Program) -> Program -> Pass Program
maybeOptimize opt f prog = do
  opt <- reader opt
  if opt then f prog else return prog

optimize :: Program -> Pass Program
optimize =
  maybeOptimize O.simplify (return . simplify) >=>
  maybeOptimize O.inlining inline              >=>
  maybeOptimize O.trimming (return . trim)     >=>
  maybeOptimize O.merge    (return . merge)    >=>
  maybeOptimize O.simplify (return . simplify)
