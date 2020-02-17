module RandC.Prism where

import RandC.Var
import RandC.Prism.Expr
import RandC.P

import Data.Text.Prettyprint.Doc

-- Assignments
--
-- (v' = e)
data Assn = Assn { aLHS :: Var
                 , aRHS :: Expr }
  deriving (Show, Eq)

instance Pretty Assn where
  pretty (Assn v e) = parens $ sep [pretty v <> pretty "'", pretty "=", pretty e]

-- Transitions
--
-- [step] c ->   p1 : (v11' = e11) & .. & (v1n' = e1n)
--             + ..
--             + pk : (vk1' = ek1) & .. & (vkl' = ekl);
data Transition = Transition { tCond :: Expr
                             , tAction :: P [Assn] }

instance Pretty Transition where
  pretty (Transition c probs) =
    sep [pretty "[step]", pretty c, pretty "->", pretty probs <> pretty ";"]

-- Variable declarations
--
-- v : [lb..ub];
data VarDecl = VarDecl { vName :: Var
                       , vLowerBound :: Int
                       , vUpperBound :: Int }

instance Pretty VarDecl where
  pretty (VarDecl v lb ub) =
    sep [pretty v, pretty ":", brackets $ cat [pretty lb, pretty "..", pretty ub]]

-- Module
--
-- module m
-- <variables>*
-- <transitions>*
-- endmodule
data Module = Module { mId :: Int
                     , mVarDecls :: [VarDecl]
                     , mTransitions :: [Transition] }

instance Pretty Module where
  pretty (Module n decls transitions) =
    vcat [ pretty "module m" <> pretty n
         , vcat $ map pretty decls
         , vcat $ map pretty transitions
         , pretty "endmodule" ]

-- Formula
--
-- formula v = e;
data Formula = Formula { fName :: Var
                       , fDef :: Expr }
  deriving (Show, Eq)

instance Pretty Formula where
  pretty (Formula v e) =
    sep [pretty "formula", pretty v, pretty "=", pretty e] <> pretty ";"

-- Program
--
-- dtmc
-- <formula>*
-- <module>*
data Program = Program [Formula] [Module]

instance Pretty Program where
  pretty (Program fs ms) =
    vcat [ pretty "dtmc"
         , vcat $ map pretty fs
         , vcat $ map pretty ms ]
