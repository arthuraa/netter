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
