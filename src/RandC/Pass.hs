{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module RandC.Pass where

import RandC.Var
import RandC.Options
import RandC.Display
import Data.Functor.Identity
import Control.Monad.Reader
import Control.Monad.Except

data Result = Done String
            | Error String
  deriving (Ord, Eq)

newtype Pass a =
  Pass (ExceptT Result (ReaderT Options (VarGenT Identity)) a)
  deriving (Functor, Applicative, Monad,
            MonadError Result, MonadReader Options,
            MonadFresh)

runPass :: Display a => Options -> Pass a -> IO ()
runPass opts (Pass f) =
  let r = fst $ runIdentity $ runVarGenT (runReaderT (runExceptT f) opts) novars in
    case r of
      Left  (Error e) -> putStrLn $ "Error: " ++ e
      Left  (Done  r) -> putStrLn r
      Right r -> putStrLn $ display r
