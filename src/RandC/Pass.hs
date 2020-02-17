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
  deriving (Ord, Eq)

newtype Pass a =
  Pass (ExceptT Result (ReaderT Options (VarGenT Identity)) a)
  deriving (Functor, Applicative, Monad,
            MonadError Result, MonadReader Options,
            MonadFresh)

ensureTarget :: Pretty a => Target -> Pass a -> Pass a
ensureTarget tgt pass = do
  tgt' <- reader target
  if tgt < tgt' then pass else do
    res <- pass
    throwError . Done . show . pretty $ res

runPass :: Pretty a => Options -> Pass a -> IO ()
runPass opts (Pass f) =
  let r = fst $ runIdentity $ runVarGenT (runReaderT (runExceptT f) opts) novars in
    case r of
      Left  (Error e) -> putStrLn $ "Error: " ++ e
      Left  (Done  r) -> putStrLn r
      Right r -> putStrLn $ show $ pretty r
