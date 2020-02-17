module RandC.Dice where

import RandC.Var
import RandC.Display
import qualified RandC.Dice.Expr  as DE

import qualified Data.Map as M

data Com = Skip
         | Assn Var DE.Expr
         | Seq Com Com
         | If DE.Expr Com Com
  deriving (Show, Eq)

data Program = Program { pVarDecls :: M.Map Var (Int, Int)
                       , pDieDecls :: M.Map DE.Die [Double]
                       , pCom :: Com }
  deriving (Show, Eq)

instance Display Program where
  display = show
