module Main where

import RandC

-- This is a tutorial on how to use RandC to write simple probabilistic
-- programs.  Since RandC is a domain-specific language embedded in Haskell,
-- some knowledge of Haskell is important to use RandC.  I'll try to explain
-- basic Haskell concepts as we go along; for a more detailed introduction, you
-- should refer to some other source, such as "Learn You a Haskell for Great
-- Good" (available for free here: http://learnyouahaskell.com/).
--
--

firstProgram :: Prog ()
firstProgram = do
  x  <-  var 1 10
  y  <-  var 1 10
  z  <-  var 2 20
  x .<-$ unif [1 .. 10]
  y .<-$ unif [1 .. 10]
  z .<-  x .+ y

main :: IO ()
main = compile firstProgram
