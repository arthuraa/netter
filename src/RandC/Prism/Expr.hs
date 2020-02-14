{-

This module contains the grammar of Prism expressions, which is shared with our
source language Imp.

-}

module RandC.Prism.Expr where

import RandC.Display
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

instance Display UnOp where
  display Not = "!"

instance Display BinOp where
  display Plus = "+"
  display Minus = "-"
  display Times = "*"
  display Div = "/"
  display Eq = "="
  display Leq = "<="
  display Lt = "<"
  display Or = "|"
  display And = "&"
  display Max = "max"
  display Min = "min"
  display Mod = "mod"

instance Display Const where
  display (Num n) = show n
  display (Bool True) = "true"
  display (Bool False) = "false"

instance Display Expr where
  display (Var v) = display v
  display (Const k) = display k
  display (UnOp o e) = display o ++ display e
  display (BinOp o e1 e2) =
    let op = display o
        x1 = display e1
        x2 = display e2 in
    if isInfix o then "(" ++ x1 ++ " " ++ op ++ " " ++ x2 ++ ")"
    else op ++ "(" ++ x1 ++ "," ++ x2 ++ ")"
  display (If cond eThen eElse) = "(" ++ display cond ++ " ? " ++ display eThen ++ " : " ++ display eElse ++ ")"

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
