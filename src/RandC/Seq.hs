module RandC.Seq where

import RandC.Var
import RandC.Prob
import qualified RandC.Prism.Expr as PE

import Data.Text.Prettyprint.Doc
import qualified Data.Map as M

data Com = Skip
         | Assn (M.Map Var PE.Expr) Com
         | If PE.Expr Com Com Com
         | Choice Var (P PE.Expr) Com
  deriving (Eq, Show)

data Program = Program { pVarDecls :: M.Map Var (Int, Int)
                       , pCom :: Com }
  deriving (Eq, Show)

instance Pretty Program where
  pretty = viaShow
