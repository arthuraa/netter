module RandC.RandImp where

import RandC.Var
import RandC.Expr hiding (If)
import RandC.P

import qualified Data.Set as S
import qualified Data.Map as M

data Program = Program { pVarDecls :: M.Map Var (Int, Int)
                       , pVarCount :: Int
                       , pComs :: [Com] }

data Com = Skip
         | Assn Var Expr
         | Seq Com Com
         | If Expr Com Com
         | Choice (P Com)
  deriving (Show, Eq)

revSeq :: [Com] -> Com
revSeq [] = Skip
revSeq [c] = c
revSeq (c : coms) = Seq (revSeq coms) c

modifiedVars :: Com -> S.Set Var
modifiedVars Skip =
  S.empty
modifiedVars (Assn v _) =
  S.singleton v
modifiedVars (Seq c1 c2) =
  modifiedVars c1 `S.union` modifiedVars c2
modifiedVars (If _ cThen cElse) =
  modifiedVars cThen `S.union` modifiedVars cElse
modifiedVars (Choice (P cs)) =
  foldl S.union S.empty [modifiedVars c| (_, c) <- cs]

type Deps = S.Set (S.Set Var)

addDeps :: S.Set Var -> Deps -> Deps
addDeps vs d =
  let (indep, dep) = S.partition (S.disjoint vs) d in
  foldl S.union vs dep `S.insert` indep

mergeDeps :: Deps -> Deps -> Deps
mergeDeps d1 d2 = foldl (flip addDeps) d1 d2

deps :: Com -> Deps
deps Skip =
  S.empty
deps (Assn v _) =
  S.singleton (S.singleton v)
deps (Seq c1 c2) =
  mergeDeps (deps c1) (deps c2)
deps (If _ c1 c2) =
  mergeDeps (deps c1) (deps c2)
deps (Choice (P choices)) =
  S.singleton $ foldl S.union S.empty [modifiedVars c | (_, c) <- choices]

project :: S.Set Var -> Com -> Com
project vs Skip =
  Skip
project vs (Assn v e)
  | v `S.member` vs = Assn v e
  | otherwise       = Skip
project vs (Seq c1 c2) =
  Seq (project vs c1) (project vs c2)
project vs (If e c1 c2) =
  If e (project vs c1) (project vs c2)
project vs c@(Choice _)
  | S.disjoint vs $ modifiedVars c = Skip
  | otherwise = c

simplify :: Com -> Com
simplify Skip =
  Skip
simplify c@(Assn _ _) =
  c
simplify (Seq c1 c2) =
  let c1' = simplify c1
      c2' = simplify c2' in
    case (c1', c2') of
      (Skip, _) -> c2'
      (_, Skip) -> c1'
      _         -> Seq c1' c2'
simplify (If e c1 c2) =
  let c1' = simplify c1
      c2' = simplify c2 in
    case e of
      Const (Bool True) -> c1'
      Const (Bool False) -> c2'
      _ -> If e c1' c2'
simplify (Choice (P choices)) =
  Choice $ P [(p, simplify c) | (p, c) <- choices]
