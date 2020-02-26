module RandC.Imp where

import RandC.Var
import RandC.Formatting
import RandC.Prism.Expr hiding (If)
import RandC.Prob hiding (Choice)

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

instance Pretty Com where
  pretty Skip          = pretty "skip"
  pretty (Assn v e)    = sep [ pretty v, pretty ".<-", pretty e ]
  pretty (Seq c1 c2)   = vcat [ pretty c1 <> pretty ";"
                              , pretty c2 ]
  pretty (If e c1 c2)  = vcat [ sep [ pretty "if", pretty e, pretty "then" ]
                              , indent 2 (pretty c1)
                              , pretty "else"
                              , indent 2 (pretty c2) ]
  pretty (Choice v es) = sep [ pretty v, pretty ".<-$", pretty es ]

instance Pretty Program where
  pretty (Program decls com) =
    vcat [ vcat [ sep [ pretty v, interval lb ub ]
                | (v, (lb, ub)) <- M.assocs decls ]
         , pretty com ]
