module RandC.UPA where

import RandC.Var
import RandC.Display
import RandC.P
import RandC.Prism.Expr

import qualified Data.Map as M

newtype Assn = Assn (M.Map Var Expr)
  deriving (Show, Eq)

data Module = Module (M.Map Var (Int, Int)) (P Assn)
  deriving (Show, Eq)

data Program = Program { pDefs :: M.Map Var Expr
                       , pMods :: [Module] }
  deriving (Show, Eq)

instance Display Assn where
  display (Assn assns) = concat [ display v ++ " = " ++ display e
                                | (v, e) <- M.assocs assns ]

instance Display Module where
  display (Module decls assns) =
    unlines $ [ "module" ] ++
              [ doDecl v lb ub | (v, (lb, ub)) <- M.assocs decls ] ++
              [ "transitions" ] ++
              [ display assns ] ++
              [ "endmodule" ]
    where doDecl v lb ub =
            concat ["var ", display v, " : [", show lb, "..", show ub, "]"]

instance Display Program where
  display (Program defs mods) =
    unlines [ concat ["def ", display v, " = ", display e]
            | (v, e) <- M.assocs defs] ++
    unlines [ display m | m <- mods ]
