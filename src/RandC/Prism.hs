module RandC.Prism where

import RandC.ToSource
import RandC.Var
import RandC.Prism.Expr
import RandC.P
import Data.List (intersperse)

-- Assignments
--
-- (v' = e)
data Assn = Assn { aLHS :: Var
                 , aRHS :: Expr }
  deriving (Show, Eq)

instance ToSource Assn where
  toSource (Assn v e) = "(" ++ show v ++ "' = " ++ show e ++ ")"

-- Transitions
--
-- [step] c ->   p1 : (v11' = e11) & .. & (v1n' = e1n)
--             + ..
--             + pk : (vk1' = ek1) & .. & (vkl' = ekl);
data Transition = Transition { tCond :: Expr
                             , tAction :: P [Assn] }

instance ToSource Transition where
  toSource (Transition c (P probs)) =
    "[step] " ++ toSource c ++ " -> " ++ doProbs probs ++ ";"
    where doProbs [] = error "Cannot have a transition with no actions"
          doProbs [(_, assns)] = doAssns assns
          doProbs probs = concat $ intersperse " + " $ map doProb probs

          doProb (prob, assns) = show prob ++ " : " ++ doAssns assns

          doAssns assns = concat $ intersperse " & " $ map toSource assns

-- Variable declarations
--
-- v : [lb..ub];
data VarDecl = VarDecl { vName :: Var
                       , vLowerBound :: Int
                       , vUpperBound :: Int }

instance ToSource VarDecl where
  toSource (VarDecl v lb ub) =
    toSource v ++ " : [" ++ show lb ++ ".." ++ show ub ++ "];"

-- Module
--
-- module m
-- <variables>*
-- <transitions>*
-- endmodule
data Module = Module { mId :: Int
                     , mVarDecls :: [VarDecl]
                     , mTransitions :: [Transition] }

instance ToSource Module where
  toSource (Module n decls transitions) =
    unlines $ [ "module m" ++ show n ] ++
              [ toSource decl | decl <- decls ] ++
              [ toSource transition | transition <- transitions ] ++
              [ "endmodule" ]

-- Program
--
-- dtmc
-- <module>*
data Program = Program [Module]

instance ToSource Program where
  toSource (Program ms) =
    unlines $ [ "dtmc" ] ++
              [ toSource m | m <- ms ]
