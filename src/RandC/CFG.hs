module RandC.CFG where

import RandC.Var
import RandC.G
import RandC.Prob
import RandC.Prism.Expr
import RandC.Formatting

import Data.Text.Prettyprint.Doc
import qualified Data.Map as M

type Id = Int

data Block = Block { bAssn :: M.Map Var (G (P Expr))
                   , bNext :: G Id }
  deriving (Eq, Show)

data Program = Program { pVarDecls :: M.Map Var (Int, Int)
                       , pDefs     :: M.Map Var Expr
                       , pMaxBlock :: Id
                       , pBlocks   :: M.Map Id Block }
  deriving (Eq, Show)

instance Pretty Block where
  pretty (Block assns next) =
    vcat [ vcat [ sep [ pretty v, pretty "=", pretty e ]
                | (v, e) <- M.assocs assns ]
         , sep [ pretty "next", pretty "=", pretty next ] ]

instance Pretty Program where
  pretty (Program decls defs maxId blocks) =
    vcat [ pretty "vars"
         , declarations decls
         , pretty "defs"
         , vcat [ sep [ pretty v, pretty "=", pretty e ]
                | (v, e) <- M.assocs defs ]
         , sep [ pretty "pc", pretty ":", interval 0 (maxId - 1), pretty ";" ]
         , pretty "blocks"
         , vcat [ vcat [ pretty "block" <+> pretty id
                       , pretty b ]
                | (id, b) <- M.assocs blocks ] ]
