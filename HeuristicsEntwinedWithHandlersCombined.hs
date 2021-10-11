{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}


module HeuristicsEntwinedWithHandlers where

import Prelude hiding (fail)
import Control.Monad.Trans (lift, MonadTrans)

data Prolog a
  deriving (Functor)

instance Applicative Prolog 
instance Monad Prolog



--- 4. Background: Handlers and Transformers

data Star f a 
  = Return a 
  | Op (f (Star f a))
  deriving (Functor, Applicative)

instance Functor f => Monad (Star f) where
  return a = Return a
  Return a >>= f = f a
  Op n >>=f = Op (fmap (>>=f) n)

data State s r
  = Get (s -> r)
  | Put s (() -> r)

instance Functor (State s) where
  fmap f (Get k) = Get (f . k)
  fmap f (Put s k) = Put s (f . k)


class Monad m => MonadState s m | m -> s where
  get :: Monad m => m s
  put :: Monad m => s -> m ()


instance MonadState s (Star (State s)) where
  get = Op (Get return)
  put s = Op (Put s return)


--- 4.1 The Free Monad Transformer

newtype StarT f m a = FreeT {unFreeT :: m (Free f a (StarT f m a))}
--deriving instance Functor (StarT f m)
--deriving instance Applicative (StarT f m)

data Free f a x 
  = ReturnF a 
  | OpF (f x)

instance Functor f => Functor (Free f a) where
  fmap _ (ReturnF a) = ReturnF a
  fmap f (OpF x) = OpF (fmap f x)


fold :: (Functor f ,Functor m, Monad m) => 
  (m (Free f a b) -> b) -> (StarT f m a -> b)
fold alg = alg . fmap (fmap (fold alg)) . unFreeT

instance (Functor f ,Functor m,Monad m) => Functor (StarT f m) where
  fmap f  s = s >>= return . f

instance (Functor f ,Functor m,Monad m) => Applicative (StarT f m) where
  pure = return
  f' <*> m = do { f <- f'; m' <- m; return $ f m'}
instance (Functor f ,Functor m,Monad m) => Monad (StarT f m) where
  return  = FreeT . return . ReturnF
  m >>= f = fold (FreeT . join . fmap (unFreeT . alg)) m
    where 
      alg (ReturnF a) = f a
      alg (OpF op) = opF op
      join x = do {a <- x; a}

opF op = FreeT (return (OpF op))

runStateF:: (Functor (State s) ,Functor m,Monad m) => 
  StarT (State s) m a -> s -> m (a,s)
runStateF p s0 = runFreeT (alg s0) p where
alg s (ReturnF x) = return (x,s)
alg s (OpF (Get k)) = runStateF (k s) s
alg s (OpF (Put s' k)) = runStateF (k ()) s'

runFreeT :: (Functor f, Functor m, Monad m) => 
  (Free f a (StarT f m a) -> m b) -> StarT f m a -> m b
runFreeT alg p = unFreeT p >>= alg

step :: (Functor f, Functor m, Monad m) =>
  StarT f m a -> (f (StarT f m a) -> StarT f m a) -> StarT f m a
step t alg = FreeT (runFreeT alg' t) where
  alg' (ReturnF x) = return (ReturnF x)
  alg' (OpF op) = unFreeT (alg op)



--- 5. Heuristics as Handlers in Haskell
--- 5.1 Step 1: Overloading


class Monad m => MonadProlog m where
  fail ::m a
  (|||)::m a -> m a -> m a


--- 5.2 Step 2: Introducing Syntax


data Or x = Or x x
orF :: Monad m => StarT Or m a -> StarT Or m a -> StarT Or m a
orF p q = opF (Or p q)

instance Functor Or where
  fmap f (Or p q) = Or (f p) (f q)



instance (MonadProlog m, MonadTrans (StarT Or)) => MonadProlog (StarT Or m) where
  fail = lift fail 
  -- this lift needed to add MonadTrans
  p ||| q = orF p q


--- 5.3 Step 3: Adding Heuristics

type Heuristic m a = MonadTrans (StarT Or) => StarT Or m a -> StarT Or m a


---Depth-Bounded Search
dbs:: MonadProlog m => Int -> Heuristic m a
dbs 0 t = fail
dbs n t = step t alg 
  where
    alg (Or x y) = (dbs (n - 1) x) ||| (dbs (n - 1) y)

---Discrepancy-Bounded Search
dibs::MonadProlog m => Int -> Heuristic m a
dibs 0 t = fail
dibs n t = step t alg 
  where
    alg (Or x y) = (dibs n x)|||(dibs (n - 1) y)

---Node-Bounded Search

class Monad m => MonadRef r m | m -> r where
  newRef :: a -> m (r a)
  readRef ::r a -> m a
  writeRef ::r a -> a -> m ()

modifyRef :: MonadRef r m => r a -> (a -> a) -> m a
modifyRef r f = do 
                  x <- readRef r
                  writeRef r (f x)
                  return x

instance (MonadRef r m, MonadTrans (StarT Or))=> MonadRef r (StarT Or m) where
  newRef x = lift (newRef x)
  readRef r = lift (readRef r)
  writeRef r x = lift (writeRef r x)

nbs::(MonadProlog m, MonadRef r m) => Int -> Heuristic m a
nbs n t = newRef n >>= go t 
  where
    go t' ref = step t' alg 
      where
        alg (Or x y) = do 
                        n <- modifyRef ref pred
                        guard (n>0)
                        go x ref ||| go y ref
        guard True      =  return ()
        guard False     =  fail

--- Failure-Bounded Search
fbs:: (MonadProlog m,MonadRef r m) => Int -> Heuristic m a
fbs n t = do 
            ref <- newRef n
            fref <- newRef False -- (a)
            x <- go ref fref t
            writeRef fref True -- (b)
            return x 
              where
                go ref' fref' t' = step t' alg
                  where 
                    alg (Or x y) = x ||| 
                      (do 
                        b <- modifyRef fref' (const False) -- (c)
                        when (not b) -- (d)
                          (do 
                            n <- modifyRef ref' pred
                            guard (n>0))
                        y)
                          where
                            guard True      =  return ()
                            guard False     =  fail
                            when p s  = if p 
                                          then s 
                                          else return ()


--- 5.4 Step 3': Adding Heuristics as Trees


dbsTree 0 = fail
dbsTree n = dbsTree (n - 1) ||| dbsTree (n - 1)

dbs' :: MonadProlog m => Int -> Heuristic m a
dbs' db t = dbsTree db \*/ t

--- type  |- f*-m = (Functor f, Functor m, Monad m)


