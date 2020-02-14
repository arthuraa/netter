module RandC.Prism where

import RandC.Display
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

instance Display Assn where
  display (Assn v e) = "(" ++ display v ++ "' = " ++ display e ++ ")"

-- Transitions
--
-- [step] c ->   p1 : (v11' = e11) & .. & (v1n' = e1n)
--             + ..
--             + pk : (vk1' = ek1) & .. & (vkl' = ekl);
data Transition = Transition { tCond :: Expr
                             , tAction :: P [Assn] }

instance Display Transition where
  display (Transition c (P probs)) =
    "[step] " ++ display c ++ " -> " ++ doProbs probs ++ ";"
    where doProbs [] =
            error "Cannot have a transition with no actions"
          doProbs [(_, assns)] =
            doAssns assns
          doProbs _ =
            concat $ intersperse " + " $ map doProb probs

          doProb (prob, assns) = show prob ++ " : " ++ doAssns assns

          doAssns assns = concat $ intersperse " & " $ map display assns

-- Variable declarations
--
-- v : [lb..ub];
data VarDecl = VarDecl { vName :: Var
                       , vLowerBound :: Int
                       , vUpperBound :: Int }

instance Display VarDecl where
  display (VarDecl v lb ub) =
    display v ++ " : [" ++ show lb ++ ".." ++ show ub ++ "];"

-- Module
--
-- module m
-- <variables>*
-- <transitions>*
-- endmodule
data Module = Module { mId :: Int
                     , mVarDecls :: [VarDecl]
                     , mTransitions :: [Transition] }

instance Display Module where
  display (Module n decls transitions) =
    unlines $ [ "module m" ++ show n ] ++
              [ display decl | decl <- decls ] ++
              [ display transition | transition <- transitions ] ++
              [ "endmodule" ]

-- Formula
--
-- formula v = e;
data Formula = Formula { fName :: Var
                       , fDef :: Expr }
  deriving (Show, Eq)

instance Display Formula where
  display (Formula v e) =
    "formula " ++ display v ++ " = " ++ display e ++ ";"

-- Program
--
-- dtmc
-- <formula>*
-- <module>*
data Program = Program [Formula] [Module]

instance Display Program where
  display (Program fs ms) =
    unlines $ [ "dtmc" ] ++
              [ display f | f <- fs ] ++
              [ display m | m <- ms ]
