module RandC.Dice.Expr where

import RandC.Var
import RandC.P
import qualified RandC.Prism.Expr as PE

import qualified Data.Map as M
import qualified Data.Set as S

type Die = Int

data Expr = Var Var
          | Const PE.Const
          | UnOp PE.UnOp Expr
          | BinOp PE.BinOp Expr Expr
          | If Expr Expr Expr
          | Choice Die [Expr]
  deriving (Show, Eq)

subst :: (Var -> Expr) -> Expr -> Expr
subst s (Var v)             = s v
subst s (Const c)           = Const c
subst s (UnOp o e)          = UnOp o (subst s e)
subst s (BinOp o e1 e2)     = BinOp o (subst s e1) (subst s e2)
subst s (If e eThen eElse) = If (subst s e) (subst s eThen) (subst s eElse)

at :: M.Map Var Expr -> Var -> Expr
at m v = M.findWithDefault (Var v) v m

dice :: Expr -> S.Set Die
dice (Var _)             = S.empty
dice (Const _)           = S.empty
dice (UnOp _ e)          = dice e
dice (BinOp _ e1 e2)     = dice e1 `S.union` dice e2
dice (If e eThen eElse) = S.unions [dice e, dice eThen, dice eElse]
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
  where go (Var v)            = PE.Var v
        go (Const c)          = PE.Const c
        go (UnOp o e)         = PE.UnOp o $ go e
        go (BinOp o e1 e2)    = PE.BinOp o (go e1) (go e2)
        go (If e eThen eElse) = PE.If (go e) (go eThen) (go eElse)
        go (Choice d es)      = go $ es !! s d

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
