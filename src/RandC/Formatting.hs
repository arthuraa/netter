module RandC.Formatting where

import RandC.Var

import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc

interval :: Int -> Int -> Doc ann
interval lb ub = brackets $ cat [pretty lb, pretty "..", pretty ub]

declarations :: M.Map Var (Int, Int) -> Doc ann
declarations ds =
  vcat [ sep [ pretty v, pretty ":", interval lb ub, pretty ";" ]
       | (v, (lb, ub)) <- M.assocs ds ]
