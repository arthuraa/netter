module RandC.Dice where

import RandC.Var
import qualified RandC.Dice.Expr  as DE

import Data.Text.Prettyprint.Doc
import qualified Data.Map.Strict as M

data Com = Skip
         | Assn Var DE.Expr
         | Seq Com Com
         | If DE.Expr Com Com
  deriving (Show, Eq)

data Program = Program { pVarDecls :: M.Map Var (Int, Int)
                       , pDieDecls :: M.Map DE.Die [Double]
                       , pCom :: Com }
  deriving (Show, Eq)

instance Pretty Program where
  pretty = viaShow
