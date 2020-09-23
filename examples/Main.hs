{-# LANGUAGE OverloadedStrings #-}

module Main where

import Netter

import Control.Monad (forM, forM_)

-- This is a tutorial on how to use Netter to write simple probabilistic
-- programs.  Since Netter is a domain-specific language embedded in Haskell, you
-- need to know some Haskell to use the language.  I'll try to explain basic
-- Haskell concepts as we go along; for a more detailed introduction, you should
-- refer to some other source, such as "Learn You a Haskell for Great Good"
-- (available for free here: http://learnyouahaskell.com/).
--
--
-- Our First Program
-- =================
--
-- Here is our first program in Netter.

firstProgram :: Prog ()
firstProgram = do
  x  <-  var 1 10       -- Declare x as a variable ranging from 1 to 10.
  y  <-  var 1 10
  z  <-  var 2 20
  x .<-$ unif [1 .. 10] -- Sample two values from [1 .. 10] uniformly and
  y .<-$ unif [1 .. 10] -- independently, storing them in x and y.
  z .<-  x .+ y         -- Add x and y, storing the result in z.

-- Because Netter is embedded in Haskell, we declare variables using a regular
-- function 'var' rather than a special syntax.  Variables are initialized with
-- their lower bounds, as in Prism.  The arrow @<-@ is Haskell syntax for
-- binding the result of a computation to a variable.  In Netter, commands,
-- variable declarations and some other operations run in a monad 'Prog', which
-- you see in the typing annotation for 'firstProgram'.  If you are still
-- learning about monads, you should think of them as a special kinds of
-- function that can perform certain side effects.  The '()' argument that you
-- see above says that 'firstProgram' does not produce any special result; the
-- only thing this function does is creating a program as a side effect.  By
-- contrast, 'var' has type @Int -> Int -> Prog Expr@, indicating that it has an
-- effect on the program that we are building and also returns something of type
-- 'Expr' (the variables that we bind to @x@, @y@ and @z@).

-- Netter operators are different from their Haskell counterparts, because they
-- run in Prism rather than in Haskell.  To avoid conflicts with Haskell
-- operators, we adopt a convention: Netter operators start with a @.@.  The
-- arrow '.<-$', for example, is a probabilistic assignment.  It is an infix
-- operator that takes to arguments: a variable to store a sample and a
-- distribution to sample from.  In this example, we sampling from uniform
-- distributions, but we can also sample from any distribution with finite
-- support.  For instance:

samplingExample :: Prog ()
samplingExample = do
  x  <-  var 1 3
  x .<-$ [(0.3, 1), (0.4, 2), (0.3, 3)]

-- Each pair @(p, v)@ says that the distribution produces the value @v@ with
-- probability @p@ (the probabilities of all the results must sum up to 1). The
-- form @x .<- e@ is a deterministic assignment, equivalent to @x .<-$ [(1.0,
-- e)]@.  Note that /any/ list of the appropriate type can go on the right-hand
-- side, which allows us to define arbitrarily complex distributions.

-- Exercise 0: Write a function 'binomial p n' that computes the binomial
-- distribution with probability parameter 'p' for 'n' throws.  You will
-- probably want to use some of these operations:
--
-- - @int :: Int -> Expr@ Convert an 'Int' to a Netter expression
--
-- - @fromIntegral :: Int -> Double@ Convert an 'Int' to a 'Double'
--
-- - @(^) :: Double -> Int -> Double@ @x ^ y@ is @x@ to the power @y@

factorial :: Int -> Double
factorial n = undefined

binomial :: Double -> Int -> [(Double, Expr)]
binomial = undefined

-- Compiling a program
-- ===================

-- To compile a Netter program, we use the 'compile' function, as shown below.
-- To see the result of the compilation, you can run @make@ in this directory
-- and open the file @examples.pm@.  As you go over this tutorial, you can
-- replace 'firstProgram' by other functions of type @Prog ()@ to see how they
-- are compiled.

-- In general, variables in the output of Netter are automatically generated,
-- because there is no way for 'var' to know the name of the variable its result
-- is bound to.  This can make the models hard to understand.  For debugging
-- purposes, Netter provides a 'namedVar' function that fixes the name of the
-- variable in the compiled code.  For instance, we can fix the name of @x@ by
-- replacing its declaration with @x <- namedVar "x" 1 10@. Try it!

main :: IO ()
main = compile network

-- Exercise 1: Open 'examples.pm' in Prism (use the graphical interface xprism).
-- Try simulating the model for a few steps: go to "Simulator > New Path" and
-- click on "Simulate" a few times.

-- Unlike most languages, programs in Netter are meant to run forever: every
-- program is implicitly enclosed in an infinite loop. When simulating a
-- program, you will notice a special @pc_0@ variable.  This variable marks the
-- point of the program that we are currently executing, with @0@ denoting the
-- initial point of the program. In the rest of this document, we'll refer to
-- each execution of a Netter program as a /cycle/.

-- Simple Imperative Programming
-- =============================
--
-- Netter has most basic operators of imperative programming.  For instance, the
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
-- distinguish Netter functions from their Haskell equivalents.

-- Exercise 2: Define a function 'exercise2' that samples two variables 'x' and
-- 'y' uniformly from 1 to 10 and stores their maximum in 'x'.  Use the if'
-- function rather than the max' function.

exercise2 :: Prog ()
exercise2 = undefined -- Fill in here

-- The 'when'' function is a variant of 'if'' that does not require an else
-- branch:

whenExample :: Prog ()
whenExample = do
  x  <-  var 1 10
  x .<-$ unif [1 .. 10]
  when' (x .<= 3) $ do
    x .<- 1

-- (Note the use of the application operator '$' to avoid wrapping the @do@
-- block in parentheses.)

-- If you want to nest conditionals, it might be better to use the 'switch'
-- function instead:

switchExample :: Prog ()
switchExample = do
  x  <-  var 1 20
  x .<-$ unif [1 .. 10]
  switch [ (x .== 2, do
               x .<- 1)
         , (x .== 4, do
               x .<- 2)
         , (orElse, do
               x .<- 5) ]

-- ('orElse' is just a synonym for @bool True@)

-- Rewards
-- =======

-- Prism allows us to check various properties of probilistic programs. For
-- instance, we might want to compute the average of some quantity.  To do this,
-- we must declare these quantities in Netter using the 'rewards' function:

rewardExample :: Prog ()
rewardExample = do
  x <- var 0 10
  y <- var 0 10
  rewards "sum" (x .+ y)

-- Data structures
-- ===============

-- Netter does not have complex data structures such as arrays, records, lists,
-- etc.: all we have are bounded integer variables.  Fortunately, we can use
-- Haskell to emulate some of this functionality.  To illustrate, let us
-- consider the model of a simple network.  The network consists of a set of
-- clients and a set of servers.  At any given moment, each client can be active
-- or inactive.  An active client is contacting exacly one server.  We can model
-- these entities with the following Haskell data types:

data Client = Client { active :: Expr
                     , server :: Expr }

data Server = Server { load :: Expr }

-- Each field corresponds to a Prism variable; hence the 'Expr' type.  The
-- 'active' field is set to either 0 or 1, representing a boolean value.  The
-- 'server' field is set to an integer id representing the server the client is
-- contacting.  The 'load' field tells how many clients the server is currently
-- serving.  Let us start by writing a function that allocates clients and
-- servers.  The 'forM' function iterates over a list and applies a function to
-- each element of the list.  It collects all the results in another list and
-- returns it.  Hence, the 'agents' function allocates a series of variables for
-- the 'active', 'server' and 'load' fields and puts them together into 'Client'
-- and 'Server' records.

nClients :: Int
nClients = 6

nServers :: Int
nServers = 4

agents :: Prog ([Client], [Server])
agents = do

  clients <- forM [0 .. nClients - 1] $ \_ -> do
    a <- var 0 1
    s <- var 0 (nServers - 1)
    return $ Client {active = a, server = s}

  servers <- forM [0 .. nServers - 1] $ \_ -> do
    l <- var 0 nClients
    return $ Server {load = l}

  return (clients, servers)

-- This function allocates the state of the system, but does not specify how the
-- state evolves.  This is the job of the next function, 'behavior'.  It works
-- as follows: on each cycle, a client has some probability of changing from
-- active to inactive, or vice-versa.  When it becomes active, we choose one
-- server at random to serve the client, and increment its 'served' field.  When
-- it becomes inactive, we decrement the served field of the corresponding
-- server.

behavior :: [Client] -> [Server] -> Prog ()
behavior clients servers = do
  forM_ clients $ \client -> do
    if' (active client .== 1)
        (do
            active client .<-$ [(0.1, 0), (0.9, 1)]
            when' (active client .== 0) $ do
              s <- servers .!!! server client
              load s .<- load s .- 1)
        (do
            active client .<-$ [(0.9, 0), (0.1, 1)]
            when' (active client .== 1) $ do
              server client .<-$ unif [0 .. int (nServers - 1)]
              s <- servers .!!! server client
              load s .<- load s .+ 1)

-- There are a few points to note here. First, the 'forM_' function is like
-- 'forM', but discards the results of each iteration. Here, we are iterating
-- over the list of clients simply to update their variables, so we don't need
-- to return anything.
--
-- When sampling a new server, we have to use the 'int (nServers - 1)' form
-- instead of just 'nServers - 1'.  Haskell knows how to convert an integer
-- literal such as '1' to a Prism expression, but this does not work for other
-- integer values.  In these cases, you need 'int'.
--
-- In Haskell, we write @l !! i@ to index the list @l@ at position @i@.  This
-- works when @i@ has type 'Int', but here we want to index the list of servers
-- with a /Prism expression/ (@server client@).  To do this, we need a different
-- operator, '.!!!'.  Roughly speaking, the program
--
-- @
-- do
--   x <- [e0 .. en] .!!! i
--   f x
-- @
--
-- is equivalent to
--
-- @
-- switch' [ (i .== 0, f e0)
--         , ..
--         , (i .== n, f en) ]
-- @

-- We now have all the pieces to complete our model:

network :: Prog ()
network = do
  (clients, servers) <- agents
  behavior clients servers

-- Exercise 3: Try simulating this model in Prism and checking how the various
-- parameters above affect its behavior.  Build the model ("Model > Build
-- model") and see how many states you get.  (If you get an error message about
-- probabilities that do not sum up to 1, try disabling the "Do probability/rate
-- checks" option in the "Options > Options" menu.  This happens because Prism
-- cannot tell that the assignments to 'load s' will never underflow.)

-- Exercise 4: Modify the network model to include a max_load reward.  This
-- reward should compute the largest load on all servers.  Simulate the model in
-- Prism and see how the reward evolves (note the reward is 0 for every program
-- point, except for the initial one).

-- State reduction
-- ===============
--
-- You might have noticed that it is hard to build the model when you increase
-- the number of clients and servers.  The more clients and servers you have,
-- the more states you need to represent the system.  Unfortunately, the number
-- of states grows exponentially with the number of nodes.  Hence, the fewer
-- variables you use to represent a system, the better.
--
-- In a real network, it would make sense for each server to have a variable
-- storing the number of active connections.  However, we do not need this
-- information in our models, since it can be computed anew from the client
-- state.
--
-- Exercise 5: Modify the 'network' and 'behavior' functions so that they do not
-- allocate the list of servers, and use only the number of servers.  Modify the
-- reward function to compute the maximum load using only the client state.  You
-- will need to use the Prism ternary operator: @cond .? eThen .: eElse@ tests
-- the Prism expression @cond@, returning @eThen@ if it the condition holds, and
-- @eElse@ otherwise.
