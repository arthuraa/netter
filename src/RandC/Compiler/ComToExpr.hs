module RandC.Compiler.ComToExpr where

import RandC.Var
import RandC.P
import RandC.Dice.Expr (at)
import qualified RandC.Dice.Expr as E
import RandC.Dice

import qualified Data.Map as M
import qualified Data.Set as S

-- Transform a command into an equivalent mapping of parallel assignments.
-- If m = compile c, then running v := val m v should have the same effect
-- on v as running c.
compile :: Com -> M.Map Var E.Expr
compile Skip         = M.empty
compile (Assn v e)   = M.singleton v e
compile (Seq c1 c2)  = let m1 = compile c1
                           m2 = M.map (E.subst $ (m1 `at`)) $ compile c2 in
                         M.unionWith (\e1 e2 -> e2) m1 m2
compile (If e c1 c2) = let m1 = compile c1
                           m2 = compile c2
                           vs = M.keysSet m1 `S.union` M.keysSet m2 in
                         M.fromSet (\v -> E.If e (m1 `at` v) (m2 `at` v)) vs

-- The specification for compile, replacing the binding map by a function.
compileF :: Com -> Var -> E.Expr
compileF Skip               v = E.Var v
compileF (Assn v' e)        v = if v == v' then e else E.Var v
compileF (Seq c1 c2)        v = E.subst (compileF c1) (compileF c2 v)
compileF (If e cThen cElse) v = E.If e (compileF cThen v) (compileF cElse v)
