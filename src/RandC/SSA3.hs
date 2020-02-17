module RandC.SSA3 where

import RandC.Var
import RandC.Formatting
import RandC.D
import qualified RandC.Prism.Expr as PE

import Data.Text.Prettyprint.Doc
import qualified Data.Map.Strict as M

type Assn = M.Map Var (D PE.Expr)
type Defs = M.Map Var PE.Expr

data Program = Program { pVarDecls :: M.Map Var (Int, Int)
                       , pDice :: M.Map Die [Double]
                       , pAssn :: Assn
                       , pDefs :: Defs }
  deriving (Show, Eq)

instance Pretty Program where
  pretty (Program decls dice assn defs) =
    vcat [ pretty "vars"
         , vcat [ sep [ pretty v, interval lb ub ] <> pretty ";"
                | (v, (lb, ub)) <- M.assocs decls]
         , pretty "dice"
         , vcat [ pretty d <+> pretty ps | (d, ps) <- M.assocs dice ]
         , pretty "assignments"
         , vcat [ sep [pretty v, pretty "=", pretty e] | (v, e) <- M.assocs assn ]
         , pretty "auxiliaries"
         , vcat [ sep [pretty v, pretty "=", pretty e] | (v, e) <- M.assocs defs ] ]
