module RandC.Dice where

import RandC.Var
import RandC.Formatting
import RandC.Prob
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

instance Pretty Com where
  pretty Skip          = pretty "skip"
  pretty (Assn v e)    = sep [ pretty v, pretty ".<-", pretty e ]
  pretty (Seq c1 c2)   = vcat [ pretty c1 <> pretty ";"
                              , pretty c2 ]
  pretty (If e c1 c2)  = vcat [ sep [ pretty "if", pretty e, pretty "then" ]
                              , indent 2 (pretty c1)
                              , pretty "else"
                              , indent 2 (pretty c2) ]

instance Pretty Program where
  pretty (Program decls dice com) =
    vcat [ pretty "vars"
         , vcat [ sep [ pretty v, interval lb ub ]
                | (v, (lb, ub)) <- M.assocs decls ]
         , line
         , pretty "dice"
         , vcat [ sep [ pretty d, pretty ps ]
                | (d, ps) <- M.assocs dice ]
         , line
         , pretty com ]
