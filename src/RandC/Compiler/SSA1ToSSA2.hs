module RandC.Compiler.SSA1ToSSA2 where

import RandC.Pass
import RandC.D
import qualified RandC.Dice.Expr  as DE
import qualified RandC.Prism.Expr as PE
import qualified RandC.SSA1       as Src
import qualified RandC.SSA2       as Tgt

import qualified Data.Map as M

compileExpr :: DE.Expr -> D PE.Expr
compileExpr (DE.Var v) =
  return $ PE.Var v
compileExpr (DE.Const c) =
  return $ PE.Const c
compileExpr (DE.UnOp o e) =
  PE.UnOp o <$> compileExpr e
compileExpr (DE.BinOp o e1 e2) =
  PE.BinOp o <$> compileExpr e1 <*> compileExpr e2
compileExpr (DE.If e eThen eElse) =
  PE.If <$> compileExpr e <*> compileExpr eThen <*> compileExpr eElse
compileExpr (DE.Choice d es) =
  Choice d $ map compileExpr es

compile :: Src.Program -> Pass Tgt.Program
compile (Src.Program decls dice assn defs) =
  return $ Tgt.Program decls dice assn (M.map compileExpr defs)
