{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module RandC.Var
  (Var,
   Vars,
   VarGen,
   VarGenT(..),
   MonadFresh,
   name,
   runVarGenT,
   novars,
   fresh,
   (|+|)) where

import Data.Text
import Data.Text.Prettyprint.Doc
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State
import Data.Functor.Identity
import qualified Data.Map.Strict as M
import qualified Data.Set as S

data Var = Var !Text !Int
  deriving (Show, Ord, Eq)

instance Pretty Var where
  pretty (Var x n) = pretty x <> pretty "_" <> pretty n

type Vars = M.Map Text Int

name :: Var -> Text
name (Var x _) = x

novars :: Vars
novars = M.empty

newtype VarGenT m a = VarGenT (StateT Vars m a)
  deriving (Applicative,Functor,Monad)

runVarGenT :: Monad m => VarGenT m a -> Vars -> m (a, Vars)
runVarGenT (VarGenT f) vs = runStateT f vs

type VarGen a = VarGenT Identity a

class Monad m => MonadFresh m where
  fresh :: Text -> m Var

instance Monad m => MonadFresh (VarGenT m) where
  fresh x = VarGenT $ do
    vs <- get
    let n = M.findWithDefault 0 x vs
    put $ M.insert x (n + 1) vs
    return $ Var x n

instance MonadState s m => MonadState s (VarGenT m) where
  state f = VarGenT $ StateT $ \vs -> do
    x <- get
    let (r, x') = f x
    put x'
    return (r, vs)

instance MonadFresh m => MonadFresh (ExceptT e m) where
  fresh x = ExceptT $ do
    v <- fresh x
    return $ Right v

instance MonadFresh m => MonadFresh (ReaderT e m) where
  fresh x = ReaderT $ \_ -> fresh x

instance MonadFresh m => MonadFresh (StateT s m) where
  fresh x = StateT $ \s -> fresh x >>= \v -> return (v, s)

(|+|) :: M.Map Var Int -> M.Map Var Int -> M.Map Var Int
cs1 |+| cs2 =
  let vs       = M.keysSet cs1 `S.union` M.keysSet cs2
      val cs v = M.findWithDefault 0 v cs in
  M.fromSet (\v -> val cs1 v + val cs2 v) vs
