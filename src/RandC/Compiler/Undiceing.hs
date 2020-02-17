module RandC.Compiler.Undiceing where

import RandC.Var
import RandC.Options
import RandC.Pass
import RandC.D
import RandC.P
import RandC.Compiler.DToP

import qualified RandC.Prism.Expr as PE
import qualified RandC.SSA3       as Src
import qualified RandC.UPA        as Tgt

import Control.Monad
import qualified Data.Map as M
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
  M.Map Die [Double] -> DepClass -> M.Map Var (D PE.Expr) -> P (M.Map Var PE.Expr)
compileDepClass probs (vs, ds) assn =
  undice probs ds $ foldM addVar M.empty $ S.toList vs
  where addVar :: M.Map Var PE.Expr -> Var -> D (M.Map Var PE.Expr)
        addVar assn' v = do
          case M.lookup v assn of
            Just e  -> M.insert v <$> e <*> pure assn'
            Nothing -> return assn'

compile :: Src.Program -> Pass Tgt.Program
compile (Src.Program decls probs assn defs) =
  let dcs = dependencies $ M.map dice assn
      decl v = case M.lookup v decls of
                 Just d  -> d
                 Nothing -> error "Unbound variable" in

    ensureTarget UPA $
    return $ Tgt.Program defs [(M.fromSet decl vs,
                                compileDepClass probs dc assn)
                              | dc@(vs, _) <- dcs]
