{-

This module contains the grammar of Prism expressions, which is shared with our
source language Imp.

-}

module RandC.Prism.Expr where

import RandC.ToSource
import RandC.Var

import qualified Data.Set as S

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
          | If Expr Expr Expr
  deriving (Show, Eq)

atomic :: Expr -> Bool
atomic (Var _)   = True
atomic (Const _) = True
atomic _         = False

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
  toSource (If cond eThen eElse) = "(" ++ toSource cond ++ " ? " ++ toSource eThen ++ " : " ++ toSource eElse ++ ")"

-- Overload arthimatic operators
instance Num Expr where
  e1 + e2 = BinOp Plus e1 e2
  e1 - e2 = BinOp Minus e1 e2
  e1 * e2 = BinOp Times e1 e2

  abs _ = undefined
  signum = undefined
  fromInteger i = Const $ Num $ fromInteger i

substM :: Monad m => (Var -> m Expr) -> Expr -> m Expr
substM s (Var v) =
  s v
substM s (Const c) =
  return $ Const c
substM s (UnOp o e) =
  UnOp o <$> substM s e
substM s (BinOp o e1 e2) =
  BinOp o <$> substM s e1 <*> substM s e2
substM s (If e eThen eElse) =
  If <$> substM s e <*> substM s eThen <*> substM s eElse

simplify :: Expr -> Expr
simplify (Var v)            = Var v
simplify (Const c)          = Const c
simplify (UnOp o e)         = UnOp o (simplify e)
simplify (BinOp o e1 e2)    = BinOp o (simplify e1) (simplify e2)
simplify (If e eThen eElse) = let e'     = simplify e
                                  eThen' = simplify eThen
                                  eElse' = simplify eElse in
                                if eThen' == eElse' then eThen'
                                else case e' of
                                  Const (Bool True) -> eThen'
                                  Const (Bool False) -> eElse'
                                  _ -> If e' eThen' eElse'

vars :: Expr -> S.Set Var
vars (Var v)            = S.singleton v
vars (Const _)          = S.empty
vars (UnOp _ e)         = vars e
vars (BinOp _ e1 e2)    = vars e1 `S.union` vars e2
vars (If e eThen eElse) = S.unions $ map vars [e, eThen, eElse]
