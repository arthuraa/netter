{-# LANGUAGE OverloadedStrings #-}
module RandC where

import RandC.Prob
import RandC.Var

import RandC.Options
import RandC.Pass
import qualified RandC.Prism.Expr as PE
import qualified RandC.Imp as Imp
import qualified RandC.Compiler as Compiler

import Data.Text
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map.Strict as M

type Expr = PE.Expr

data S = S { sVarDecls :: M.Map Var (Int, Int)
           , sFormulas :: M.Map Var Expr
           , sComs :: [Imp.Com] }

type Comp a = StateT S Pass a

-- TODO: Find a way of deprecating this
num :: Int -> Expr
num = PE.Const . PE.Int

int :: Int -> Expr
int = num

double :: Double -> Expr
double = PE.Const . PE.Double

namedVar :: Text -> Int -> Int -> Comp Expr
namedVar x lb ub = do
  when (lb > ub) $ throwError $ Error $
    "Invalid bounds for variable " ++ unpack x ++ ": " ++
    show lb ++ ">" ++ show ub

  v <- fresh x

  S decls defs coms <- get

  let decls' = M.insert v (lb, ub) decls

  put $ S decls' defs coms

  return $ PE.Var v

var :: Int -> Int -> Comp Expr
var = namedVar "_"

formula :: Text -> Expr -> Comp Expr
formula x e = do
  v <- fresh x

  S decls defs coms <- get

  let defs' = M.insert v e defs

  put $ S decls defs' coms

  return $ PE.Var v

-- Assignment operator used for Var
infix 1 .<-
(.<-) :: Expr -> Expr -> Comp ()
PE.Var v .<- rhs = do
  S decls defs coms <- get

  when (not $ M.member v decls) $ do
    throwError $ Error $ "Attempt to assign to a non-variable " ++ show v

  put $ S decls defs (Imp.Com [Imp.Assn (M.singleton v (return $ return rhs))] : coms)

e .<- _rhs = throwError $ Error $ "Attempt to assign to non-variable " ++ show e

infix 1 .?
(.?) :: Expr -> Expr -> Expr -> Expr
e .? eThen = PE.If e eThen

infix 0 .:
(.:) :: (Expr -> Expr) -> Expr -> Expr
(.:) = id

infix 1 .<-$
(.<-$) :: Expr -> [(Double, Expr)] -> Comp ()
PE.Var v .<-$ rhs = do
  S decls defs coms <- get

  when (not $ M.member v decls) $ do
    throwError $ Error $ "Attempt to assign to a non-variable " ++ show v

  put $ S decls defs (Imp.Com [Imp.Assn (M.singleton v (return $ P rhs))] : coms)

e .<-$ _rhs = throwError $ Error $ "Attempt to assign to non-variable " ++ show e

if' :: Expr -> Comp () -> Comp () -> Comp ()
if' e cThen cElse = do
  S decls defs coms <- get

  put $ S decls defs []
  cThen

  S decls' defsThen comsThen <- get

  put $ S decls' defsThen []
  cElse

  S decls'' defsElse comsElse <- get

  put $ S decls'' defsElse (Imp.Com [Imp.If e (Imp.revSeq comsThen) (Imp.revSeq comsElse)] : coms)

switch :: [(Expr, Comp ())] -> Comp ()
switch [] = return ()
switch ((cond, e) : branches) = if' cond e (switch branches)

orElse :: Expr
orElse = PE.Const (PE.Bool True)

when' :: Expr -> Comp () -> Comp ()
when' e c = if' e c (return ())

max' :: Expr -> Expr -> Expr
max' = PE.BinOp PE.Max

min' :: Expr -> Expr -> Expr
min' = PE.BinOp PE.Min

mod' :: Expr -> Expr -> Expr
mod' = PE.BinOp PE.Mod

infixr 3 .&&
(.&&) :: Expr -> Expr -> Expr
(.&&) = PE.BinOp PE.And

infixr 2 .||
(.||) :: Expr -> Expr -> Expr
(.||) = PE.BinOp PE.Or

infixl 7 .*
(.*) :: Expr -> Expr -> Expr
(.*) = PE.BinOp PE.Times

infixl 7 ./
(./) :: Expr -> Expr -> Expr
(./) = PE.BinOp PE.Div

infixl 6 .+
(.+) :: Expr -> Expr -> Expr
(.+) = PE.BinOp PE.Plus

infixl 6 .-
(.-) :: Expr -> Expr -> Expr
(.-) = PE.BinOp PE.Minus

infix 4 .==
(.==) :: Expr -> Expr -> Expr
e1 .== e2 = PE.BinOp PE.Eq e1 e2

infix 4 ./=
(./=) :: Expr -> Expr -> Expr
e1 ./= e2 = PE.UnOp PE.Not (e1 .== e2)

infix 4 .<=
(.<=) :: Expr -> Expr -> Expr
(.<=) = PE.BinOp PE.Leq

infix 4 .<
(.<) :: Expr -> Expr -> Expr
(.<) = PE.BinOp PE.Lt

compileWith :: Options -> Comp () -> IO ()
compileWith opts prog = doPass opts $ do
  ((), S decls defs coms) <- runStateT prog $ S M.empty M.empty []
  Compiler.compile (Imp.Program decls defs (Imp.revSeq coms))

compile :: Comp () -> IO ()
compile prog = do
  opts <- readOptions
  compileWith opts prog
