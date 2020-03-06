module RandC.Linear where

import RandC.Var
import RandC.Prism.Expr
import RandC.Prob
import RandC.G
import RandC.Formatting

import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc

type Block = M.Map Var (G (P Expr))

data Program = Program { pVarDecls :: M.Map Var (Int, Int)
                       , pDefs :: M.Map Var Expr
                       , pBlocks :: [Block] }
  deriving (Eq, Show)

instance Pretty Program where
  pretty (Program decls defs blocks) =
    vcat [ pretty "vars"
         , declarations decls
         , pretty "defs"
         , vcat [ pretty v <+> pretty "=" <+> pretty e
                | (v, e) <- M.assocs defs ]
         , pretty "blocks"
         , line
         , vcat [ vcat [ pretty "block"
                       , vcat [ pretty v <+> pretty "=" <+> pretty e
                              | (v, e) <- M.assocs block ] ]
                | block <- blocks ] ]
