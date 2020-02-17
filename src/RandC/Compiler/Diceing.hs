module RandC.Compiler.Diceing where

import RandC.Var
import RandC.P
import qualified RandC.Dice.Expr  as DE
import qualified RandC.Prism.Expr as PE
import qualified RandC.Imp        as S
import qualified RandC.Dice       as T

import qualified Data.Map as M
import Control.Monad.ST
import Data.STRef

compileExpr :: PE.Expr -> DE.Expr
compileExpr (PE.Var v) =
  DE.Var v
compileExpr (PE.Const c) =
  DE.Const c
compileExpr (PE.UnOp o e) =
  DE.UnOp o (compileExpr e)
compileExpr (PE.BinOp o e1 e2) =
  DE.BinOp o (compileExpr e1) (compileExpr e2)
compileExpr (PE.If e eThen eElse) =
  DE.If (compileExpr e) (compileExpr eThen) (compileExpr eElse)

compile :: S.Program -> VarGen T.Program
compile (S.Program varDecls com) = return $ runST $ do
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
        return $ T.Assn v (DE.Choice d [compileExpr e | (_, e) <- es])

  com' <- compileCom com
  ds   <- readSTRef dice

  return $ T.Program varDecls ds com'
