module RandC.SSA3 where

import RandC.Var

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
  pretty = viaShow
