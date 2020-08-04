{-# LANGUAGE RecordWildCards #-}

module RandC.CFG where

import RandC.Var
import RandC.G
import RandC.Prob
import RandC.Prism.Expr
import RandC.Formatting

import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import qualified Data.Map as M

type Id = Int

data Block = Block { bAssn :: M.Map Var (G (P Expr))
                   , bNext :: G Id }
  deriving (Eq, Show)

data Program = Program { pVarDecls :: M.Map Var (Int, Int)
                       , pDefs     :: Locals
                       , pRewards  :: M.Map Text Expr
                       , pMaxBlock :: Id
                       , pBlocks   :: M.Map Id Block }
  deriving (Eq, Show)

instance Pretty Block where
  pretty (Block assns next) =
    vcat [ vcat [ sep [ pretty v, pretty "=", pretty e ]
                | (v, e) <- M.assocs assns ]
         , sep [ pretty "next", pretty "=", pretty next ] ]

instance Pretty Program where
  pretty Program{..} =
    vcat [ pretty "vars"
         , declarations pVarDecls
         , pretty "defs"
         , vcat [ sep [ pretty v, pretty "=", pretty e ]
                | (v, (e, _)) <- M.assocs $ defs pDefs ]
         , pretty "rewards"
         , vcat [ sep [ pretty v, pretty "=", pretty e ]
                | (v, e) <- M.assocs pRewards ]
         , sep [ pretty "pc", pretty ":",
                 interval 0 (pMaxBlock - 1), pretty ";" ]
         , pretty "blocks"
         , vcat [ vcat [ pretty "block" <+> pretty id
                       , pretty b ]
                | (id, b) <- M.assocs pBlocks ] ]
