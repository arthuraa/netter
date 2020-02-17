module RandC.Formatting where

import Data.Text.Prettyprint.Doc

interval :: Int -> Int -> Doc ann
interval lb ub = brackets $ cat [pretty lb, pretty "..", pretty ub]
