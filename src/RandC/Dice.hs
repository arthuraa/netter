module RandC.Dice where

import RandC.Var
import RandC.D
import qualified RandC.Prism.Expr as PE

import Data.Text.Prettyprint.Doc
import qualified Data.Map.Strict as M

data Com = Skip
         | Assn Var (D PE.Expr)
         | Seq Com Com
         | If (D PE.Expr) Com Com
  deriving (Show, Eq)

data Program = Program { pVarDecls :: M.Map Var (Int, Int)
                       , pDieDecls :: M.Map Die [Double]
                       , pCom :: Com }
  deriving (Show, Eq)

instance Pretty Program where
  pretty = viaShow
