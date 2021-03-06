{-# LANGUAGE RecordWildCards #-}

module Netter.UPA where

import Netter.Var
import Netter.Prob
import Netter.Prism.Expr

import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import qualified Data.Map.Strict as M

newtype Assn = Assn (M.Map Var Expr)
  deriving (Show, Eq)

data Module = Module (M.Map Var (Int, Int)) [(Expr, P Assn)]
  deriving (Show, Eq)

data Program = Program { pDefs :: Locals
                       , pRewards :: M.Map Text [(Expr, Expr)]
                       , pMods :: [Module] }
  deriving (Show, Eq)

instance Pretty Assn where
  pretty (Assn assns) =
    hcat $ punctuate (pretty " & ") $ [ sep [pretty v, pretty "=", pretty e]
                                      | (v, e) <- M.assocs assns ]

instance Pretty Module where
  pretty (Module decls assns) =
    vcat [ pretty "module"
         , vcat [ doDecl v lb ub | (v, (lb, ub)) <- M.assocs decls ]
         , pretty "transitions"
         , vcat [ sep [pretty guard, pretty "->", pretty assn]
                | (guard, assn) <- assns ]
         , pretty "endmodule" ]
    where doDecl v lb ub =
            sep [pretty "var", pretty v, pretty ":",
                 brackets $ cat [pretty lb, pretty "..", pretty ub]]

instance Pretty Program where
  pretty Program{..} =
    vcat $ [ sep [pretty "def", pretty v, pretty "=", pretty e]
           | (v, (e, _)) <- M.assocs $ defs pDefs] ++
           [ sep [pretty "reward", pretty v, pretty "=", pretty e]
           | (v, e) <- M.assocs pRewards] ++
           map pretty pMods
