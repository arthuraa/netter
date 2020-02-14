module RandC.UPA where

import RandC.Var
import RandC.P
import RandC.Prism.Expr

import qualified Data.Map as M

type Module = (M.Map Var (Int, Int), P (M.Map Var Expr))

data Program = Program { pDefs :: M.Map Var Expr
                       , pMods :: [Module] }
  deriving (Show, Eq)
