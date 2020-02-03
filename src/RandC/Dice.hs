module RandC.Dice where

import RandC.Var
import RandC.P
import qualified RandC.Dice.Expr  as DE
import qualified RandC.Prism.Expr as PE
import qualified RandC.Imp as Imp

import qualified Data.Map as M
import qualified Data.Set as S

data Com = Skip
         | Assn Var DE.Expr
         | Seq Com Com
         | If DE.Expr Com Com
  deriving (Show, Eq)

data Program = Program { pVarDecls :: M.Map Var (Int, Int)
                       , pDieDecls :: M.Map DE.Die [Double]
                       , pCom :: Com }
  deriving (Show, Eq)

-- Transform a command into an equivalent mapping of parallel assignments.
-- If m = flatten c, then running v := val m v should have the same effect
-- on v as running c.
flatten :: Com -> M.Map Var DE.Expr
flatten Skip         = M.empty
flatten (Assn v e)   = M.singleton v e
flatten (Seq c1 c2)  = let m1  = flatten c1
                           m2  = M.map (DE.subst $ DE.at m1) $ flatten c2 in
                         M.unionWith (\e1 e2 -> e2) m1 m2
flatten (If e c1 c2) = let m1 = flatten c1
                           m2 = flatten c2
                           vs = M.keysSet m1 `S.union` M.keysSet m2 in
                         M.fromSet (\v -> DE.If e (m1 `DE.at` v) (m2 `DE.at` v)) vs

-- The specification for flatten, replacing the binding map by a function.
flattenF :: Com -> Var -> DE.Expr
flattenF Skip               v = DE.Var v
flattenF (Assn v' e)        v = if v == v' then e else DE.Var v
flattenF (Seq c1 c2)        v = DE.subst (flattenF c1) (flattenF c2 v)
flattenF (If e cThen cElse) v = DE.If e (flattenF cThen v) (flattenF cElse v)
