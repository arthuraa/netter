module RandC.Compiler.DiceToSSA1 where

import RandC.Var
import RandC.Options
import RandC.Pass
import qualified RandC.Dice.Expr as DE
import qualified RandC.Dice      as Src
import qualified RandC.SSA1      as Tgt

import Control.Monad (foldM)
import qualified Data.Map.Strict as M
import qualified Data.Set as S

compileCom :: Src.Com -> Pass (Tgt.Assn, Tgt.Defs)
compileCom Src.Skip =
  return (M.empty, M.empty)
compileCom (Src.Assn v e) = do
  v' <- fresh (name v)
  return (M.singleton v v', M.singleton v' e)
compileCom (Src.Seq c1 c2) = do
  (assn1, defs1) <- compileCom c1
  (assn2, defs2) <- compileCom c2

  let assn = M.unionWith (\_ v -> v) assn1 assn2

  let getVar1 v = DE.Var $ M.findWithDefault v v assn1

  let defs2' = M.map (DE.subst getVar1) defs2

  let defs   = M.union defs1 defs2'

  return (assn, defs)
compileCom (Src.If e cThen cElse) = do
  (assnThen, defsThen) <- compileCom cThen
  (assnElse, defsElse) <- compileCom cElse

  ve <- fresh "c"

  let mergeVar (assn, defs) v =
        case (M.lookup v assnThen, M.lookup v assnElse) of
          (Just vThen, Just vElse) -> do
            v' <- fresh (name v)
            let ve' = DE.If (DE.Var ve) (DE.Var vThen) (DE.Var vElse)
            return (M.insert v v' assn, M.insert v' ve' defs)
          (Just v', _) -> do
            return (M.insert v v' assn, defs)
          (_, Just v') -> do
            return (M.insert v v' assn, defs)
          (_, _) -> error "DiceToSSA: Attempted to merge inexisting variable"

  let defs = M.unions [defsThen, defsElse, M.singleton ve e]

  let vars = M.keysSet assnThen `S.union` M.keysSet assnElse

  foldM mergeVar (M.empty, defs) $ S.toList vars

compile :: Src.Program -> Pass Tgt.Program
compile (Src.Program vars dice c) = ensureTarget SSA1 $ do
  (assn, defs) <- compileCom c
  return $ Tgt.Program vars dice assn defs
