{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-

This module contains the grammar of Prism expressions, which is shared with our
source language Imp.

-}

module RandC.Prism.Expr where


import RandC.Var

import GHC.Generics
import Data.HashCons
import Data.Functor.Identity
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text.Prettyprint.Doc

data Const = Int Int | Double Double | Bool Bool
  deriving (Show, Ord, Eq, Generic)

instance Hashable Const

data UnOp = Not | Floor | Ceil | Round
  deriving (Show, Ord, Eq, Generic)

instance Hashable UnOp

data BinOp = Plus | Minus | Times | Div | Eq | Leq | Lt | Or | And | Max | Min | Mod | Pow | Log
  deriving (Show, Ord, Eq, Generic)

instance Hashable BinOp

isInfix :: BinOp -> Bool
isInfix o = o `elem` [Plus, Minus, Times, Div, Leq, Lt, Eq, Or, And]

newtype Expr = Expr (HC Expr')
  deriving (Show, Ord, Eq, Generic, Hashable)

data Expr' = Var' !Var
           | Const' !Const
           | UnOp' !UnOp !Expr
           | BinOp' !BinOp !Expr !Expr
           | If' !Expr !Expr !Expr
  deriving (Show, Ord, Eq, Generic)

instance Hashable Expr'

instance HashCons Expr'

{-# COMPLETE Var, Const, UnOp, BinOp, If #-}
pattern Var :: Var -> Expr
pattern Var x <- Expr (getVal -> Var' x)
  where Var x = Expr (hc $ Var' x)

pattern Const :: Const -> Expr
pattern Const c <- Expr (getVal -> Const' c)
  where Const c = Expr (hc $ Const' c)

pattern UnOp :: UnOp -> Expr -> Expr
pattern UnOp o e <- Expr (getVal -> UnOp' o e)
  where UnOp o e = Expr (hc $ UnOp' o e)

pattern BinOp :: BinOp -> Expr -> Expr -> Expr
pattern BinOp o e1 e2 <- Expr (getVal -> BinOp' o e1 e2)
  where BinOp o e1 e2 = Expr (hc $ BinOp' o e1 e2)

pattern If :: Expr -> Expr -> Expr -> Expr
pattern If e e1 e2 <- Expr (getVal -> If' e e1 e2)
  where If e e1 e2 = Expr (hc $ If' e e1 e2)

atomic :: Expr -> Bool
atomic (Var _)   = True
atomic (Const _) = True
atomic _         = False

instance Pretty UnOp where
  pretty Not   = pretty "!"
  pretty Floor = pretty "floor"
  pretty Ceil  = pretty "ceil"
  pretty Round = pretty "round"

instance Pretty BinOp where
  pretty o = pretty $ go o
    where go Plus  = "+"
          go Minus = "-"
          go Times = "*"
          go Div   = "/"
          go Eq    = "="
          go Leq   = "<="
          go Lt    = "<"
          go Or    = "|"
          go And   = "&"
          go Max   = "max"
          go Min   = "min"
          go Mod   = "mod"
          go Pow   = "pow"
          go Log   = "log"

instance Pretty Const where
  pretty (Int n) = pretty n
  pretty (Double x) = pretty x
  pretty (Bool True) = pretty "true"
  pretty (Bool False) = pretty "false"

instance Pretty Expr where
  pretty (Var v) = pretty v
  pretty (Const k) = pretty k
  pretty (UnOp Not (BinOp Eq e1 e2)) =
    parens $ cat [pretty e1, pretty "!=", pretty e2]
  pretty (UnOp o e) = cat [pretty o, pretty e]
  pretty (BinOp o e1 e2) =
    let op = pretty o
        x1 = pretty e1
        x2 = pretty e2 in
    if isInfix o then parens $ cat [x1, op, x2]
    else cat [op, tupled [x1, x2]]
  pretty (If cond eThen eElse) =
    parens $ cat [pretty cond, pretty "?", pretty eThen, pretty ":", pretty eElse]

conj :: [Expr] -> Expr
conj []       = Const $ Bool True
conj (e : es) = foldl (BinOp And) e es

-- Overload arthimatic operators
instance Num Expr where
  e1 + e2 = BinOp Plus e1 e2
  e1 - e2 = BinOp Minus e1 e2
  e1 * e2 = BinOp Times e1 e2

  abs _ = undefined
  signum = undefined
  fromInteger i = Const $ Int $ fromInteger i

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
simplify1 o e@(Const (Bool b)) =
  case o of
    Not -> Const (Bool (not b))
    _   -> error $ "Expr: found ill-typed expression " ++ show (pretty (UnOp o e))
simplify1 o e@(Const (Int _)) =
  case o of
    Ceil  -> e
    Floor -> e
    Round -> e
    _   -> error $ "Expr: found ill-typed expression " ++ show (pretty (UnOp o e))
simplify1 o e@(Const (Double x)) =
  case o of
    Ceil  -> Const $ Int $ ceiling x
    Floor -> Const $ Int $ floor x
    Round -> Const $ Int $ round x
    _     -> error $ "Expr: found ill-typed expression " ++ show (pretty (UnOp o e))
simplify1 o e = UnOp o e

simplify2 :: BinOp -> Expr -> Expr -> Expr
simplify2 o e1@(Const (Int n1)) e2@(Const (Int n2)) =
  let int    f = Const $ Int    $ f n1 n2
      double f = Const $ Double $ f (fromIntegral n1) (fromIntegral n2)
      bool   f = Const $ Bool   $ f n1 n2 in
  case o of
    Plus  -> int    (+)
    Minus -> int    (-)
    Times -> int    (*)
    Div   -> double (/)
    Eq    -> bool   (==)
    Leq   -> bool   (<=)
    Lt    -> bool   (<)
    Max   -> int    max
    Min   -> int    min
    Mod   -> int    mod
    Pow   -> int    (^)
    Log   -> double logBase
    _     -> error $ "Expr: found ill-typed expression " ++ show (pretty (BinOp o e1 e2))
simplify2 o e1@(Const (Double _)) (Const (Int n2)) =
  simplify2 o e1 (Const $ Int $ fromIntegral n2)
simplify2 o (Const (Int n1)) e2@(Const (Double _)) =
  simplify2 o (Const $ Int $ fromIntegral n1) e2
simplify2 o e1@(Const (Double n1)) e2@(Const (Double n2)) =
  let double f = Const $ Double $ f n1 n2
      bool   f = Const $ Bool   $ f n1 n2 in
  case o of
    Plus  -> double (+)
    Minus -> double (-)
    Times -> double (*)
    Div   -> double (/)
    Eq    -> bool   (==)
    Leq   -> bool   (<=)
    Lt    -> bool   (<)
    Max   -> double max
    Min   -> double min
    Pow   -> double (**)
    Log   -> double logBase
    _     -> error $ "Expr: found ill-typed expression " ++ show (pretty (BinOp o e1 e2))
simplify2 o e1@(Const (Bool b1)) e2@(Const (Bool b2)) =
  let bool f = Const $ Bool $ f b1 b2 in
  case o of
    Eq  -> bool (==)
    And -> bool (&&)
    Or  -> bool (||)
    _   -> error $ "Expr: found ill-typed expression " ++ show (pretty (BinOp o e1 e2))
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

-- | Compute all of the variables that appear on an expression.
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
counts (BinOp _ e1 e2)    = counts e1 |+| counts e2
counts (If e eThen eElse) = counts e |+| counts eThen |+| counts eElse
