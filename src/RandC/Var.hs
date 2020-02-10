{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module RandC.Var (Var, Vars, VarT, runVarT, novars, fresh) where

import RandC.ToSource

import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as M

data Var = Var String Int
  deriving (Show, Ord, Eq)

instance ToSource Var where
  toSource (Var x n) = x ++ "_" ++ show n

type Vars = M.Map String Int

novars :: Vars
novars = M.empty

newtype VarT m a = VarT (StateT Vars m a)
  deriving (Applicative,Functor,Monad)

runVarT :: Monad m => VarT m a -> Vars -> m (a, Vars)
runVarT (VarT f) vs = runStateT f vs

class Monad m => MonadFresh m where
  fresh :: String -> m Var

instance Monad m => MonadFresh (VarT m) where
  fresh x = VarT $ do
    vs <- get
    let n = M.findWithDefault 0 x vs
    put $ M.insert x (n + 1) vs
    return $ Var x n

instance MonadState s m => MonadState s (VarT m) where
  state f = VarT $ StateT $ \vs -> do
    x <- get
    let (r, x') = f x
    put x'
    return (r, vs)

instance MonadFresh m => MonadFresh (ExceptT e m) where
  fresh x = ExceptT $ do
    v <- fresh x
    return $ Right v
