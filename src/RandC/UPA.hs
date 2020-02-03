module RandC.UPA where

import RandC.Var
import RandC.P
import RandC.Prism.Expr

import qualified Data.Map as M

type Module = (M.Map Var (Int, Int), P (M.Map Var Expr))

type Program = [Module]
