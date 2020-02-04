module RandC.Imp where

import RandC.Var
import RandC.Prism.Expr hiding (If)
import RandC.P

import qualified Data.Map as M

data Program = Program { pVarDecls :: M.Map Var (Int, Int)
                       , pCom :: Com }

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
