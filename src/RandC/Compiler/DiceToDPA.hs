module RandC.Compiler.DiceToDPA where

import RandC.Var
import RandC.Dice.Expr (at)
import qualified RandC.Dice.Expr as E
import qualified RandC.Dice as Src
import qualified RandC.DPA  as Tgt

import qualified Data.Map as M
import qualified Data.Set as S

-- Transform a command into an equivalent mapping of parallel assignments.
-- If m = compile c, then running v := val m v should have the same effect
-- on v as running c.
compileCom :: Src.Com -> M.Map Var E.Expr
compileCom Src.Skip =
  M.empty
compileCom (Src.Assn v e) =
  M.singleton v e
compileCom (Src.Seq c1 c2) =
  let m1 = compileCom c1
      m2 = M.map (E.subst $ (m1 `at`)) $ compileCom c2 in
    M.unionWith (\_ e2 -> e2) m1 m2
compileCom (Src.If e c1 c2) =
  let m1 = compileCom c1
      m2 = compileCom c2
      vs = M.keysSet m1 `S.union` M.keysSet m2 in
    M.fromSet (\v -> E.If e (m1 `at` v) (m2 `at` v)) vs

compile :: Src.Program -> Tgt.Program
compile (Src.Program decls dice com) = Tgt.Program decls dice (compileCom com)
