{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module RandC.Pass where

import RandC.Var
import RandC.Options
import Data.Functor.Identity
import Data.Text.Prettyprint.Doc
import Control.Monad.Reader
import Control.Monad.Except

data Result = Done String
            | Error String
  deriving (Ord, Eq, Show)

newtype Pass a =
  Pass (ExceptT Result (ReaderT Options (VarGenT Identity)) a)
  deriving (Functor, Applicative, Monad,
            MonadError Result, MonadReader Options,
            MonadFresh)

ensureTarget :: Pretty a => Target -> a -> Pass a
ensureTarget curTgt res = do
  endTgt <- reader target
  if curTgt <= endTgt then return res
    else throwError . Done . show . pretty $ res

runPass :: Options -> Pass a -> Either Result a
runPass opts (Pass f) =
  fst $ runIdentity $ runVarGenT (runReaderT (runExceptT f) opts) novars

doPass :: Pretty a => Options -> Pass a -> IO ()
doPass opts pass =
  case runPass opts pass of
    Left  (Error e) -> putStrLn $ "Error: " ++ e
    Left  (Done  r) -> putStrLn r
    Right r -> putStrLn $ show $ pretty r
