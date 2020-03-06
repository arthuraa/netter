module RandC.Linear where

import RandC.Var
import RandC.Prism.Expr
import RandC.Prob

import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc

-- A guarded probabilistic expression
type GPExpr = ([Expr], P Expr)
type Block = M.Map Var [GPExpr]

data Program = Program { pVarDecls :: M.Map Var (Int, Int)
                       , pDefs :: M.Map Var Expr
                       , pBlocks :: [Block] }
  deriving (Eq, Show)

instance Pretty Program where
  pretty = viaShow
