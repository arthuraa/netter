{-# LANGUAGE RecordWildCards, OverloadedStrings #-}

module RandC.Prism where

import RandC.Var
import RandC.Prism.Expr
import RandC.Prob

import Data.Text (Text)
import Data.Text.Prettyprint.Doc

-- Assignments
--
-- (v' = e)
data Assn = Assn { aLHS :: Var
                 , aRHS :: Expr }
  deriving (Show, Eq)

instance Pretty Assn where
  pretty (Assn v e) = parens $ sep [pretty v <> "'", "=", pretty e]

newtype Assns = Assns [Assn]

instance Pretty Assns where
  pretty (Assns []) = "true"
  pretty (Assns assns) =
    encloseSep "" "" "&" $ map pretty assns

-- Transitions
--
-- [step] c ->   p1 : (v11' = e11) & .. & (v1n' = e1n)
--             + ..
--             + pk : (vk1' = ek1) & .. & (vkl' = ekl);
data Transition = Transition { tCond :: Expr
                             , tAction :: P Assns }

instance Pretty Transition where
  pretty (Transition c probs) =
    sep ["[step]", pretty c, "->", pretty probs <> ";"]

-- Variable declarations
--
-- v : [lb..ub];
data VarDecl = VarDecl { vName :: Var
                       , vLowerBound :: Int
                       , vUpperBound :: Int }

instance Pretty VarDecl where
  pretty (VarDecl v lb ub) =
    sep [pretty v,
         ":", brackets $ cat [pretty lb, "..", pretty ub]]
    <> ";"

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
    vcat [ "module m" <> pretty n
         , vcat $ map pretty decls
         , vcat $ map pretty transitions
         , "endmodule" ]

-- Formula
--
-- formula v = e;
data Formula = Formula { fName :: Var
                       , fDef :: Expr }
  deriving (Show, Eq)

instance Pretty Formula where
  pretty (Formula v e) =
    sep ["formula", pretty v, "=", pretty e] <> ";"

-- Reward
-- rewards "r"
--   [step] c1 -> e1;
--   ..
--   [step] cn -> en;
-- endrewards

data Rewards = Rewards { rName    :: Text
                       , rClauses :: [(Expr, Expr)] }

instance Pretty Rewards where
  pretty Rewards{..} =
    vcat [ "rewards" <+> dquotes (pretty rName)
         , vcat [ pretty cond <+> ":" <+> pretty e <+> ";"
                | (cond, e) <- rClauses ]
         , "endrewards" ]

-- Program
--
-- dtmc
-- <formula>*
-- <module>*
data Program = Program { pFormulas :: [Formula]
                       , pRewards  :: [Rewards]
                       , pMods     :: [Module] }

instance Pretty Program where
  pretty Program{..} =
    vcat [ "dtmc"
         , vcat $ map pretty pFormulas
         , vcat $ map pretty pMods
         , vcat $ map pretty pRewards ]
