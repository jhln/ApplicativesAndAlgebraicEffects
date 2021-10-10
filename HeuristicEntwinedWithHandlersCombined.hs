{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}

module HeuristicsEntwinedWithHandlers where

import Prelude hiding (fmap)

data Prolog a
  deriving (Functor)

instance Applicative Prolog 
instance Monad Prolog

--fail :: Prolog a

data FStar f a 
  = Return a 
  | Op (f (FStar f a))
  deriving (Functor, Applicative)

class Monad m => MonadState s m | m -> s where
  --get :: Monad m => m s
  --put :: Monad m => s -> m ()

instance Functor f => Monad (FStar f') where
  return a = Return a
  Return a >>= f = f a
  Op n >>=f = Op (fmap (>>=f) n)

data State s r
  = Get (s -> r)
  | Put s (() -> r)
instance Functor (State s) where

instance MonadState s ((State s)) where
get = Op (Get return)
put s = Op (Put s return)

fmap f (Get k) = Get (f . k)
fmap f (Put s k) = Put s (f . k)