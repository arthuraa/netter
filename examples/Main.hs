{-# LANGUAGE OverloadedStrings #-}

module Main where

import RandC

-- This is a tutorial on how to use RandC to write simple probabilistic
-- programs.  Since RandC is a domain-specific language embedded in Haskell, you
-- need to know some Haskell to use the language.  I'll try to explain basic
-- Haskell concepts as we go along; for a more detailed introduction, you should
-- refer to some other source, such as "Learn You a Haskell for Great Good"
-- (available for free here: http://learnyouahaskell.com/).
--
--
-- Our First Program
-- =================
--
-- Here is our first program in RandC.

firstProgram :: Prog ()
firstProgram = do
  x  <-  var 1 10       -- Declare x as a variable ranging from 1 to 10.
  y  <-  var 1 10
  z  <-  var 2 20
  x .<-$ unif [1 .. 10] -- Sample two values from [1 .. 10] uniformly and
  y .<-$ unif [1 .. 10] -- independently, storing them in x and y.
  z .<-  x .+ y         -- Add x and y, storing the result in z.

-- Because RandC is embedded in Haskell, we declare variables using a regular
-- function 'var' rather than a special syntax.  The arrow @<-@ is Haskell
-- syntax for binding the result of a computation to a variable.  In RandC,
-- commands, variable declarations and some other operations run in a monad
-- 'Prog', which you see in the typing annotation for 'firstProgram'.  If you
-- are still learning about monads, you should think of them as a special kinds
-- of function that can perform certain side effects.  The '()' argument that
-- you see above says that 'firstProgram' does not produce any special result;
-- the only thing this function does is creating a program as a side effect.  By
-- contrast, 'var' has type @Int -> Int -> Prog Expr@, indicating that it has an
-- effect on the program that we are building and also returns something of type
-- 'Expr' (the variables that we bind to @x@, @y@ and @z@).

-- RandC operators are different from their Haskell counterparts, because they
-- run in Prism rather than in Haskell.  To avoid conflicts with Haskell
-- operators, we adopt a convention: RandC operators start with a @.@.  The
-- arrow '.<-$', for example, is a probabilistic assignment.  It is an infix
-- operator that takes to arguments: a variable to store a sample and a
-- distribution to sample from.  In this example, we sampling from uniform
-- distributions, but we can also sample from any distribution with finite
-- support.  For instance, @x .<-$ [(0.3, 1), (0.7, 2)]@ samples @1@ with
-- probability @0.3@ and @0.7@ with the remaining probability. The form @x .<-
-- e@ is a deterministic assignment, equivalent to @x .<-$ [(1.0, e)]@.

-- To compile a RandC program, we use the 'compile' function, as shown below.
-- To see the result of the compilation, you can run @make@ in this directory
-- and open the file @examples.pm@.  As you go over this tutorial, you can
-- replace 'firstProgram' by other functions of type @Prog ()@ to see how they
-- are compiled.

-- In general, variables in the output of RandC are automatically generated,
-- because there is no way for 'var' to know the name of the variable its result
-- is bound to.  This can make the models hard to understand.  For debugging
-- purposes, RandC provides a 'namedVar' function that fixes the name of the
-- variable in the compiled code.  For instance, we can fix the name of @x@ by
-- replacing its declaration with @x <- namedVar "x" 1 10@. Try it!

main :: IO ()
main = compile firstProgram

-- Exercise 1: Open 'examples.pm' in Prism (use the graphical interface xprism).
-- Try simulating the model for a few steps: go to "Simulator > New Path" and
-- click on "Simulate" a few times.


-- Simple Imperative Programming
-- =============================
--
-- RandC has most basic operators of imperative programming.  For instance, the
-- 'if'' function allows us to run code conditionally:

ifExample :: Prog ()
ifExample = do
  x  <-  var 1 10
  y  <-  var 1 10
  x .<-$ unif [1 .. 10]
  if' (x .<= 3)
    (do
       y .<-$ unif [1 .. 3])
    (do
       y .<- x .- 2)

-- Note that this is not the same as Haskell's own if statement:

haskellIf :: Int -> Int -> Int
haskellIf x y = if x <= 3 then y else x - 2

-- The condition in the second if must be an expression of type 'Bool'.  When
-- building a Prism model, we don't know in advance what the expression @x .<=
-- 3@ will evaluate to, because @x@ is not set yet -- this will only happen when
-- running the model checker.  By contrast, when evaluating 'haskellIf' on some
-- arguments, we can perform the test @x <= 3@ and decide which branch we need
-- to execute.  Whenever needed, we use primed names (if', when', max', etc.) to
-- distinguish RandC functions from their Haskell equivalents.

-- Exercise 2: Define a function 'exercise2' that samples two variables 'x' and
-- 'y' uniformly from 1 to 10 and stores their maximum in 'x'.  Use the if'
-- function rather than the max' function.

exercise2 :: Prog ()
exercise2 = undefined -- Fill in here

-- The 'when'' function is a variant of 'if'' that does not require an else
-- branch:

whenExample :: Prog ()
whenExample = do
  x  <- var 1 10
  x .<- unif [1 .. 10]
  when' (x .<= 3) $ do
    x .<- 1

-- (Note the use of the application operator '$' to avoid wrapping the @do@
-- block in parentheses.)

-- If you want to nest conditionals, it might be better to use the 'switch'
-- function instead:

switchExample :: Prod ()
switchExample = do
  x  <- var 1 20
  x .<- unif [1 .. 10]
  switch [ (x .== 2, do
               x .<- 1)
         , (x .== 4, do
               x .<- 2)
         , (orElse, do
               x .<- 5) ]

-- ('orElse' is just a synonym for @bool True@)
