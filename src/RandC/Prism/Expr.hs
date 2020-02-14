{-

This module contains the grammar of Prism expressions, which is shared with our
source language Imp.

-}

module RandC.Prism.Expr where

import RandC.Display
import RandC.Var

import Data.Functor.Identity
import qualified Data.Map as M
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
substM s e = go e
  where go (Var v)            = s v
        go (Const c)          = return $ Const c
        go (UnOp o e)         = UnOp o <$> go e
        go (BinOp o e1 e2)    = BinOp o <$> go e1 <*> go e2
        go (If e eThen eElse) = If <$> go e <*> go eThen <*> go eElse

subst1M :: Monad m => Var -> m Expr -> Expr -> m Expr
subst1M v e = substM (\v' -> if v == v' then e else return $ Var v')

subst :: (Var -> Expr) -> Expr -> Expr
subst s = runIdentity . substM (return . s)

subst1 :: Var -> Expr -> Expr -> Expr
subst1 v e e' = runIdentity $ subst1M v (return e) e'

simplify1 :: UnOp -> Expr -> Expr
simplify1 Not (Const (Bool b)) = Const (Bool (not b))
simplify1 o e = UnOp o e

simplify2 :: BinOp -> Expr -> Expr -> Expr
simplify2 o e1@(Const (Num n1)) e2@(Const (Num n2)) =
  let num  f = Const $ Num  $ f n1 n2
      bool f = Const $ Bool $ f n1 n2 in
  case o of
    Plus  -> num  (+)
    Minus -> num  (-)
    Times -> num  (*)
    Div   -> num  div
    Eq    -> bool (==)
    Leq   -> bool (<=)
    Lt    -> bool (<)
    Max   -> num  max
    Min   -> num  min
    Mod   -> num  mod
    _     -> error $ "Expr: found ill-typed expression " ++ display (BinOp o e1 e2)
simplify2 o e1@(Const (Bool b1)) e2@(Const (Bool b2)) =
  let bool f = Const $ Bool $ f b1 b2 in
  case o of
    Eq  -> bool (==)
    And -> bool (&&)
    Or  -> bool (||)
    _   -> error $ "Expr: found ill-typed expression " ++ display (BinOp o e1 e2)
simplify2 Eq e1 e2
  | e1 == e2 = Const $ Bool $ True
simplify2 Leq e1 e2
  | e1 == e2 = Const $ Bool $ True
simplify2 Lt e1 e2
  | e1 == e2 = Const $ Bool $ False
simplify2 o e1 e2 = BinOp o e1 e2

simplify :: Expr -> Expr
simplify (Var v)            = Var v
simplify (Const c)          = Const c
simplify (UnOp o e)         = simplify1 o (simplify e)
simplify (BinOp o e1 e2)    = simplify2 o (simplify e1) (simplify e2)
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

counts :: Expr -> M.Map Var Int
counts (Var v)            = M.singleton v 1
counts (Const _)          = M.empty
counts (UnOp _ e)         = counts e
counts (BinOp _ e1 e2)    = counts e1 <+> counts e2
counts (If e eThen eElse) = counts e <+> counts eThen <+> counts eElse
