module RandC.DieImp where

import RandC.Var
import qualified RandC.Expr as Expr
import qualified RandC.RandImp as Imp

import qualified Data.Map as M

type Die = Int

data Expr = Var Var
          | Const Expr.Const
          | UnOp Expr.UnOp Expr
          | BinOp Expr.BinOp Expr Expr
          | IfE Expr Expr Expr
          | Choice Die [Expr]
  deriving (Show, Eq)

data Com = Skip
         | Assn Var Expr
         | Seq Com Com
         | If Expr Com Com
  deriving (Show, Eq)

data Program = Program { pVarDecls :: M.Map Var (Int, Int)
                       , pDieDecls :: M.Map Die [Double]
                       , pCom :: Com }
  deriving (Show, Eq)
