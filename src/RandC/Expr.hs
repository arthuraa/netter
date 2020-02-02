module RandC.Expr where

import RandC.ToSource
import RandC.Var

data Const = Num Int | Bool Bool
  deriving (Show, Eq)

data UnOp = Not
  deriving (Show, Eq)

data BinOp = Plus | Minus | Times | Div | Eq | Leq | Lt | Or | And | Max | Min | Mod
  deriving (Show, Eq)

isInfix :: BinOp -> Bool
isInfix o = o `elem` [Plus, Minus, Times, Div, Leq, Lt, Eq, Or, And]

data Expr = Var Var
          | Const Const
          | UnOp UnOp Expr
          | BinOp BinOp Expr Expr
          | IfE Expr Expr Expr
  deriving (Show, Eq)

instance ToSource UnOp where
  toSource Not = "!"

instance ToSource BinOp where
  toSource Plus = "+"
  toSource Minus = "-"
  toSource Times = "*"
  toSource Div = "/"
  toSource Eq = "="
  toSource Leq = "<="
  toSource Lt = "<"
  toSource Or = "|"
  toSource And = "&"
  toSource Max = "max"
  toSource Min = "min"
  toSource Mod = "mod"

instance ToSource Const where
  toSource (Num n) = show n
  toSource (Bool True) = "true"
  toSource (Bool False) = "false"

instance ToSource Expr where
  toSource (Var v) = toSource v
  toSource (Const k) = toSource k
  toSource (UnOp o e) = toSource o ++ toSource e
  toSource (BinOp o e1 e2) =
    let op = toSource o
        x1 = toSource e1
        x2 = toSource e2 in
    if isInfix o then "(" ++ x1 ++ " " ++ op ++ " " ++ x2 ++ ")"
    else op ++ "(" ++ x1 ++ "," ++ x2 ++ ")"
  toSource (IfE cond eThen eElse) = "(" ++ toSource cond ++ " ? " ++ toSource eThen ++ " : " ++ toSource eElse ++ ")"
