{-# LANGUAGE RecordWildCards #-}

module RandC.Imp where

import RandC.Var
import RandC.Formatting
import RandC.Prism.Expr hiding (If)
import RandC.G hiding (If)
import RandC.Prob hiding (Choice)

import Data.Text (Text)
import Data.Text.Prettyprint.Doc hiding (cat)
import qualified Data.Map.Strict as M

data Program = Program { pVarDecls :: M.Map Var (Int, Int)
                       , pDefs :: M.Map Var Expr
                       , pRewards :: M.Map Text Expr
                       , pCom :: Com }
  deriving (Show, Eq)

data Instr = Assn (M.Map Var (G (P Expr)))
           | If Expr Com Com
  deriving (Eq, Show)

newtype Com = Com { instrs :: [Instr] }
  deriving (Eq, Show)

skip :: Com
skip = Com []

cat :: Com -> Com -> Com
cat c1 c2 = Com $ instrs c1 ++ instrs c2

revSeq :: [Com] -> Com
revSeq cs = foldl cat skip $ reverse cs

instance Pretty Instr where
  pretty (Assn assns) =
    vcat [ pretty "assn"
         , vcat [ sep [ pretty v, pretty ".<-", pretty e ]
                | (v, e) <- M.assocs assns ] ]
  pretty (If e c1 c2) =
    vcat [ sep [ pretty "if", pretty e, pretty "then" ]
         , indent 2 (pretty c1)
         , pretty "else"
         , indent 2 (pretty c2)
         , pretty "fi" ]

instance Pretty Com where
  pretty (Com is) = vcat [ pretty i <> pretty ";" | i <- is ]

instance Pretty Program where
  pretty Program{..} =
    vcat [ declarations pVarDecls
         , vcat [ sep [ pretty "def", pretty v, pretty "=", pretty e, pretty ";" ]
                | (v, e) <- M.assocs pDefs ]
         , vcat [ sep [ pretty "reward", pretty v, pretty "=", pretty e, pretty ";" ]
                | (v, e) <- M.assocs pRewards ]
         , pretty pCom ]
