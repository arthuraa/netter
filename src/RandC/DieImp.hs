module RandC.DieImp where

import RandC.Var
import RandC.P
import qualified RandC.Prism.Expr as PE
import qualified RandC.Imp as Imp

import qualified Data.Map as M
import qualified Data.Set as S

type Die = Int

data Expr = Var Var
          | Const PE.Const
          | UnOp PE.UnOp Expr
          | BinOp PE.BinOp Expr Expr
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

subst :: (Var -> Expr) -> Expr -> Expr
subst s (Var v)             = s v
subst s (Const c)           = Const c
subst s (UnOp o e)          = UnOp o (subst s e)
subst s (BinOp o e1 e2)     = BinOp o (subst s e1) (subst s e2)
subst s (IfE e eThen eElse) = IfE (subst s e) (subst s eThen) (subst s eElse)

at :: M.Map Var Expr -> Var -> Expr
at m v = M.findWithDefault (Var v) v m

-- Transform a command into an equivalent mapping of parallel assignments.
-- If m = flatten c, then running v := val m v should have the same effect
-- on v as running c.
flatten :: Com -> M.Map Var Expr
flatten Skip         = M.empty
flatten (Assn v e)   = M.singleton v e
flatten (Seq c1 c2)  = let m1  = flatten c1
                           m2  = M.map (subst $ at m1) $ flatten c2 in
                         M.unionWith (\e1 e2 -> e2) m1 m2
flatten (If e c1 c2) = let m1 = flatten c1
                           m2 = flatten c2
                           vs = M.keysSet m1 `S.union` M.keysSet m2 in
                         M.fromSet (\v -> IfE e (m1 `at` v) (m2 `at` v)) vs

-- The specification for flatten, replacing the binding map by a function.
flattenF :: Com -> Var -> Expr
flattenF Skip               v = Var v
flattenF (Assn v' e)        v = if v == v' then e else Var v
flattenF (Seq c1 c2)        v = subst (flattenF c1) (flattenF c2 v)
flattenF (If e cThen cElse) v = IfE e (flattenF cThen v) (flattenF cElse v)

dice :: Expr -> S.Set Die
dice (Var _)             = S.empty
dice (Const _)           = S.empty
dice (UnOp _ e)          = dice e
dice (BinOp _ e1 e2)     = dice e1 `S.union` dice e2
dice (IfE e eThen eElse) = S.unions [dice e, dice eThen, dice eElse]
dice (Choice d es)       = d `S.insert` S.unions [dice e | e <- es]

type Valuation = Die -> Int

addVal :: Valuation -> Die -> Int -> Valuation
addVal s d i d'
  | d == d' = i
  | otherwise = s d'

-- Convert an expression with dice into a deterministic expression given a
-- valuation s for the die values.
compileExpr :: Valuation -> Expr -> PE.Expr
compileExpr s e = go e
  where go (Var v)             = PE.Var v
        go (Const c)           = PE.Const c
        go (UnOp o e)          = PE.UnOp o $ go e
        go (BinOp o e1 e2)     = PE.BinOp o (go e1) (go e2)
        go (IfE e eThen eElse) = PE.If (go e) (go eThen) (go eElse)
        go (Choice d es)       = go $ es !! s d

marginalize :: M.Map Die [Double] -> S.Set Die -> P Valuation
marginalize probs ds = foldl go (return $ const 0) $ S.toList ds
  where go distr d =
          case M.lookup d probs of
            Just dProbs -> do
              dVal <- P $ zip dProbs [0..]
              s    <- distr
              return $ addVal s d dVal

            Nothing ->
              error $ "Assertion failed: die " ++ show d ++ " is unbound"

compileDepClass ::
  M.Map Die [Double] ->
  S.Set Var ->
  S.Set Die ->
  M.Map Var Expr ->
  P (M.Map Var PE.Expr)
compileDepClass probs vs ds m = do
  s <- marginalize probs ds
  return $ M.fromSet (\v -> compileExpr s $ m `at` v) vs
