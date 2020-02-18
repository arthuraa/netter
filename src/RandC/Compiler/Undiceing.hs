module RandC.Compiler.Undiceing where

import RandC.Var
import RandC.Options
import RandC.Pass
import RandC.Prob

import qualified RandC.Prism.Expr as PE
import qualified RandC.SSA2       as Src
import qualified RandC.UPA        as Tgt

import Control.Monad
import qualified Data.Map.Strict as M
import qualified Data.Set as S

type DepClass = (S.Set Var, S.Set Die)

dependencies :: M.Map Var (S.Set Die) -> [DepClass]
dependencies = M.foldrWithKey (\v ds -> addDeps (S.singleton v, ds)) []
  where addDeps (vs, ds) [] = [(vs, ds)]
        addDeps (vs, ds) ((vs', ds') : rest)
          | S.disjoint ds ds' =
            (vs', ds') : addDeps (vs, ds) rest
          | otherwise =
            addDeps (vs `S.union` vs', ds `S.union` ds') rest

compileDepClass ::
  M.Map Die [Double] -> DepClass -> M.Map Var (D PE.Expr) -> P Tgt.Assn
compileDepClass probs (vs, ds) assn =
  undice probs ds $ foldM addVar (Tgt.Assn M.empty) $ S.toList vs
  where addVar :: Tgt.Assn -> Var -> D Tgt.Assn
        addVar (Tgt.Assn assn') v = do
          case M.lookup v assn of
            Just e  -> Tgt.Assn <$> (M.insert v <$> e <*> pure assn')
            Nothing -> return $ Tgt.Assn assn'

compile :: Src.Program -> Pass Tgt.Program
compile (Src.Program decls probs assn defs) =
  let dcs = dependencies $ M.map dice assn
      decl v = case M.lookup v decls of
                 Just d  -> d
                 Nothing -> error "Unbound variable" in

    ensureTarget UPA $
    return $ Tgt.Program defs [Tgt.Module (M.fromSet decl vs)
                                (compileDepClass probs dc assn)
                              | dc@(vs, _) <- dcs]
