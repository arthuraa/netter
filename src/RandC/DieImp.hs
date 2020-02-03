module RandC.DieImp where

import RandC.Var
import qualified RandC.Expr as Expr
import qualified RandC.RandImp as Imp

import qualified Data.Map as M
import qualified Data.Set as S

type Die = Int

data Expr = Var Var
          | Const Expr.Const
          | UnOp Expr.UnOp Expr
          | BinOp Expr.BinOp Expr Expr
          | IfE Expr Expr Expr
          | Choice Die [Expr]
  deriving (Show, Eq)

data Com = Skip
         | Assn Var Expr
         | Seq Com Com
         | If Expr Com Com
  deriving (Show, Eq)

data Program = Program { pVarDecls :: M.Map Var (Int, Int)
                       , pDieDecls :: M.Map Die [Double]
                       , pCom :: Com }
  deriving (Show, Eq)

subst :: (Var -> Expr) -> Expr -> Expr
subst s (Var v)             = s v
subst s (Const c)           = Const c
subst s (UnOp o e)          = UnOp o (subst s e)
subst s (BinOp o e1 e2)     = BinOp o (subst s e1) (subst s e2)
subst s (IfE e eThen eElse) = IfE (subst s e) (subst s eThen) (subst s eElse)

modifiedVars :: Com -> S.Set Var
modifiedVars Skip         = S.empty
modifiedVars (Assn v _)   = S.singleton v
modifiedVars (Seq c1 c2)  = modifiedVars c1 `S.union` modifiedVars c2
modifiedVars (If _ c1 c2) = modifiedVars c1 `S.union` modifiedVars c2

val :: M.Map Var Expr -> Var -> Expr
val m v = M.findWithDefault (Var v) v m

flatten :: Com -> M.Map Var Expr
flatten Skip         = M.empty
flatten (Assn v e)   = M.singleton v e
flatten (Seq c1 c2)  = let m1  = flatten c1
                           m2  = M.map (subst $ val m1) $ flatten c2 in
                         M.unionWith (\e1 e2 -> e2) m1 m2
flatten (If e c1 c2) = let m1 = flatten c1
                           m2 = flatten c2
                           vs = M.keysSet m1 `S.union` M.keysSet m2 in
                         M.fromSet (\v -> IfE e (val m1 v) (val m2 v)) vs

-- The specification for flatten, replacing the binding map by a function.
flattenF :: Com -> Var -> Expr
flattenF Skip               v = Var v
flattenF (Assn v' e)        v = if v == v' then e else Var v
flattenF (Seq c1 c2)        v = subst (flattenF c1) (flattenF c2 v)
flattenF (If e cThen cElse) v = IfE e (flattenF cThen v) (flattenF cElse v)
