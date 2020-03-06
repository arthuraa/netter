{-# LANGUAGE OverloadedStrings #-}
module RandC.Compiler.LinearToUPA where

import RandC.Var
import RandC.Options
import RandC.Pass
import RandC.Prism.Expr as PE
import qualified RandC.Linear as Src
import qualified RandC.UPA    as Tgt

import qualified Data.Set        as S
import qualified Data.Map.Strict as M

type Assn = M.Map Var (M.Map Int [Src.GPExpr])

addBlock :: Assn -> (Int, Src.Block) -> Assn
addBlock assn (pc, block) =
  M.unionWith M.union assn (M.map (M.singleton pc) block)

check :: Var -> Int -> Expr
check v n = BinOp Eq (Var v) (Const (Num n))

pcModule :: Var -> Int -> Tgt.Module
pcModule pc maxPc =
  let assn = M.singleton pc $ BinOp Mod (Var pc) (Const $ Num maxPc) in
  Tgt.Module (M.singleton pc (0, maxPc - 1))
             [(Const $ Bool True, return $ Tgt.Assn assn)]

compile :: Src.Program -> Pass Tgt.Program
compile prog = do

  Src.Program decls defs blocks <- ensureTarget UPA prog

  pc <- fresh "pc"

  let maxPc = length blocks

  let assnMap = foldl addBlock M.empty $ zip [0..] blocks

  let allPCs  = S.fromList [0 .. maxPc - 1]

  let actions v =
        let assns        = M.findWithDefault M.empty v assnMap
            constantPCs  = S.difference allPCs $ M.keysSet assns
            defaultGuard =
              if constantPCs == S.empty then []
              else
                [foldl (BinOp And) (Const $ Bool True)
                 [UnOp Not $ check pc n | n <- M.keys assns]] in
          [ (guard, return $ Tgt.Assn M.empty) | guard <- defaultGuard ] ++
          [ (guard, fmap (Tgt.Assn . M.singleton v) e)
          | (n, assns) <- M.assocs assns,
            (guards, e) <- assns,
            let guard = conj (check pc n : guards) ]

  let modules = [ Tgt.Module (M.singleton v (lb, ub)) (actions v)
                | (v, (lb, ub)) <- M.assocs decls ]

  return $ Tgt.Program defs modules
