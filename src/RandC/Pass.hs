{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module RandC.Pass where

import RandC.Var
import RandC.Options
import Data.Functor.Identity
import Data.Text.Prettyprint.Doc
import Control.Monad.Reader
import Control.Monad.Except
import System.IO
import System.Exit

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

doOutput :: Maybe String -> String -> IO ()
doOutput Nothing  res = putStrLn res
doOutput (Just f) res =
  withFile f WriteMode $ \h -> hPutStrLn h res

doPass :: Pretty a => Options -> Pass a -> IO ()
doPass opts pass =
  case runPass opts pass of
    Left  (Error e) -> do
      hPutStrLn stderr $ "Error: " ++ e
      exitWith $ ExitFailure (-1)
    Left  (Done  r) -> doOutput (output opts) r
    Right r         -> doOutput (output opts) $ show $ pretty r
