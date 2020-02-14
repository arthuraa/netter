module RandC.SSA2 where

import RandC.Var
import RandC.D
import qualified RandC.Prism.Expr as PE

import qualified Data.Map as M

type Assn = M.Map Var Var
type Defs = M.Map Var (D PE.Expr)

data Program = Program { pVarDecls :: M.Map Var (Int, Int)
                       , pDice :: M.Map Die [Double]
                       , pAssn :: Assn
                       , pDefs :: Defs }
  deriving (Show, Eq)
