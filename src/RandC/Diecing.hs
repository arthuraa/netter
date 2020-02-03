module RandC.Diecing where

import RandC.Var
import RandC.P
import qualified RandC.Expr    as Expr
import qualified RandC.RandImp as S
import qualified RandC.DieImp  as T

import qualified Data.Map as M
import Control.Monad.ST
import Data.STRef

compileExpr :: Expr.Expr -> T.Expr
compileExpr (Expr.Var v) =
  T.Var v
compileExpr (Expr.Const c) =
  T.Const c
compileExpr (Expr.UnOp o e) =
  T.UnOp o (compileExpr e)
compileExpr (Expr.BinOp o e1 e2) =
  T.BinOp o (compileExpr e1) (compileExpr e2)
compileExpr (Expr.If e eThen eElse) =
  T.IfE (compileExpr e) (compileExpr eThen) (compileExpr eElse)

compile :: S.Program -> T.Program
compile (S.Program varDecls com) = runST $ do
  diceCount <- newSTRef 0
  dice      <- newSTRef M.empty

  let newDie ps = do
        c  <- readSTRef diceCount
        ds <- readSTRef dice
        writeSTRef diceCount $ c + 1
        writeSTRef dice      $ M.insert c ps ds
        return c

  let compileCom S.Skip =
        return $ T.Skip

      compileCom (S.Assn v e) =
        return $ T.Assn v (compileExpr e)

      compileCom (S.Seq c1 c2) = do
        c1' <- compileCom c1
        c2' <- compileCom c2
        return $ T.Seq c1' c2'

      compileCom (S.If e cThen cElse) = do
        cThen' <- compileCom cThen
        cElse' <- compileCom cElse
        return $ T.If (compileExpr e) cThen' cElse'

      compileCom (S.Choice v (P es)) = do
        d <- newDie $ map fst es
        return $ T.Assn v (T.Choice d [compileExpr e | (_, e) <- es])

  com' <- compileCom com
  ds   <- readSTRef dice

  return $ T.Program varDecls ds com'
