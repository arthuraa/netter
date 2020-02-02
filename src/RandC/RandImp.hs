module RandC.RandImp where

import RandC.Var
import RandC.Expr
import RandC.P

import qualified Data.Set as S

data Com = Skip
         | Assn Var Expr
         | Seq Com Com
         | If Expr Com Com
         | Choice (P Com)
  deriving (Show, Eq)

modifiedVars :: Com -> S.Set Var
modifiedVars Skip = S.empty
modifiedVars (Assn v _) = S.singleton v
modifiedVars (Seq c1 c2) = modifiedVars c1 `S.union` modifiedVars c2
modifiedVars (If _ cThen cElse) = modifiedVars cThen `S.union` modifiedVars cElse
modifiedVars (Choice (P cs)) = foldl S.union S.empty [modifiedVars c| (_, c) <- cs]
