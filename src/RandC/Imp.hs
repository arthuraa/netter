module RandC.Imp where

import RandC.Var
import RandC.Prism.Expr hiding (If)
import RandC.Prob

import Data.Text.Prettyprint.Doc
import qualified Data.Map.Strict as M

data Program = Program { pVarDecls :: M.Map Var (Int, Int)
                       , pCom :: Com }
  deriving (Show, Eq)

data Com = Skip
         | Assn Var Expr
         | Seq Com Com
         | If Expr Com Com
         | Choice Var (P Expr)
  deriving (Show, Eq)

revSeq :: [Com] -> Com
revSeq [] = Skip
revSeq [c] = c
revSeq (c : coms) = Seq (revSeq coms) c

instance Pretty Program where
  pretty = viaShow
