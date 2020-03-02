module RandC.CFG where

import RandC.Var
import RandC.G
import RandC.Prob
import RandC.Prism.Expr

import Data.Text.Prettyprint.Doc
import qualified Data.Map as M

type Id = Int

data Block = Block { bAssn :: P (M.Map Var Expr)
                   , bNext :: G Id }
  deriving (Eq, Show)

data Program = Program { pVarDecls :: M.Map Var (Int, Int)
                       , pMaxBlock :: Id
                       , pBlocks   :: M.Map Id Block }
  deriving (Eq, Show)

instance Pretty Program where
  pretty = viaShow
