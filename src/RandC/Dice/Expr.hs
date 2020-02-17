module RandC.Dice.Expr where

import RandC.Var
import qualified RandC.Prism.Expr as PE

import qualified Data.Map.Strict as M
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
subst s (Var v)            = s v
subst _ (Const c)          = Const c
subst s (UnOp o e)         = UnOp o (subst s e)
subst s (BinOp o e1 e2)    = BinOp o (subst s e1) (subst s e2)
subst s (If e eThen eElse) = If (subst s e) (subst s eThen) (subst s eElse)
subst s (Choice d es)      = Choice d [subst s e | e <- es]

at :: M.Map Var Expr -> Var -> Expr
at m v = M.findWithDefault (Var v) v m

dice :: Expr -> S.Set Die
dice (Var _)            = S.empty
dice (Const _)          = S.empty
dice (UnOp _ e)         = dice e
dice (BinOp _ e1 e2)    = dice e1 `S.union` dice e2
dice (If e eThen eElse) = S.unions [dice e, dice eThen, dice eElse]
dice (Choice d es)      = d `S.insert` S.unions [dice e | e <- es]
