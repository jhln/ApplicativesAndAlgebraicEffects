{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}

module MonadTransformersAndModularAlgebraicEffects where

import Prelude hiding (Maybe, Nothing, Just, MonadFail, fail)

--- 2 Monads and Monad Transformers
--- 2.1 Functors and Monads

newtype State s a = State {runState :: s -> (a,s)}

instance Functor (State s) where
  fmap f s = s >>= return . f

instance Applicative (State s) where
  pure = return
  f' <*> s' = do { f <- f'; s <- s'; return $ f s}
  -- why not ? (State f) <*> s = fmap f s

instance Monad (State s) where
  return x = State (\s -> (x, s))
  State p >>= k = State (\s -> 
                    let (x,s') = p s in
                      runState (k x) s')

class Monad m => MonadState s m | m -> s where
  get :: m s
  put :: s -> m ()


instance MonadState s (State s) where
  get = State (\ s -> (s,s))
  put s' = State (\ _ -> ((),s'))


--- 2.2 Monad Transformers

newtype StateT s m a = StateT {runStateT :: s -> m (a,s)}

class Trans t where
  lift :: Monad m => m a -> t m a

instance Trans (StateT s) where
  lift m = StateT (\ s -> m >>= \ a -> return (a,s))

instance Monad m => Functor (StateT s m) where
  fmap f s = s >>= return . f

instance Monad m => Applicative (StateT s m) where
  pure = return
  f' <*> s' = do { f <- f'; s <- s'; return $ f s}

instance Monad m => Monad (StateT s m) where
  return x = StateT (\ s -> return (x,s))
  StateT p >>= k = StateT (\ s -> do 
                                    (x,s') <- p s
                                    runStateT (k x) s')

instance Monad m => MonadState s (StateT s m) where
  get = StateT (\ s -> return (s,s))
  put s' = StateT (\ _ -> return ((),s'))

incr :: MonadState Int m => m ()
incr = get >>= put . succ

instance Functor Id where
  fmap f s = s >>= return . f

instance Applicative Id where
  pure = return
  f' <*> s' = do { f <- f'; s <- s'; return $ f s}

newtype Id a = Id {runId :: a}
instance Monad Id where
  return = Id
  Id x >>= f = f x

class Monad m => MonadFail m where
  fail :: m a

data Maybe a = Nothing | Just a
  deriving Show

instance Functor Maybe where
  fmap f s = s >>= return . f

instance Applicative Maybe where
  pure = return
  f' <*> s' = do { f <- f'; s <- s'; return $ f s}

instance Monad Maybe where
  return = Just
  Nothing >>= f = Nothing
  Just x >>= f = f x

instance MonadFail Maybe where
  fail = Nothing


newtype MaybeT m a = MaybeT {runMaybeT :: m (Maybe a)}

instance Monad m => Functor (MaybeT m) where
  fmap f s = s >>= return . f

instance Monad m => Applicative (MaybeT m) where
  pure = return
  f' <*> s' = do { f <- f'; s <- s'; return $ f s}

instance Monad m => Monad (MaybeT m) where
  return x = MaybeT (return (Just x))
  MaybeT mmx >>= f = 
            MaybeT (do 
              mx <- mmx 
              case mx of
                Nothing -> return Nothing
                Just x  -> runMaybeT (f x))

instance Monad m => MonadFail (MaybeT m) where
  fail = MaybeT (return Nothing)

instance Trans MaybeT where
  lift mx = MaybeT (fmap Just mx)


prog :: (MonadFail m, MonadState Int m) => m ()
prog = incr >> fail >> incr

instance MonadFail m => MonadFail (StateT s m) where
  fail = lift fail

exec1 :: Num s => StateT s (MaybeT Id) a -> Maybe (a, s)
exec1 prog = (runId . runMaybeT . flip runStateT 0) prog
call1 :: Maybe ((), Int)
call1 = exec1 prog

instance MonadState s m => MonadState s (MaybeT m) where
  get = lift get
  put = lift . put

--exec1 :: Num s => StateT s (MaybeT Id) a -> Maybe (a, s)
exec2 :: Num s => MaybeT (StateT s Id) a -> (Maybe a, s)
exec2 prog = (runId . flip runStateT 0 . runMaybeT) prog
--call1 :: Maybe ((), Int)
call2 :: (Maybe (), Int)
call2 = exec2 prog



--- 3 Modular Algebraic Effects
--- 3.1 Algebraic Effects


data SIG a b k = OP a (b -> k)

instance Functor (SIG a b) where
  fmap f (OP i k) = OP i (f . k)

data STATE s k 
  = GET (s -> k) 
  | PUT s (() -> k)
  deriving Functor

data Free sig a
  = Var a
  | Op (sig (Free sig a))

instance Functor f => Functor (Free f) where
  fmap f s = s >>= return . f

instance Functor f => Applicative (Free f) where
  pure = return
  f' <*> s' = do { f <- f'; s <- s'; return $ f s}

instance Functor f => Monad (Free f) where
  return x = Var x
  Var x >>= f = f x
  Op op >>= f = Op (fmap (>>=f ) op)

get' :: Free (STATE s) s
get' = Op (GET return)

put' :: s -> Free (STATE s) ()
put' s = Op (PUT s return)

incr' :: Free (STATE Int) ()
incr' = get' >>= put' . succ

fold :: Functor sig 
  => (a -> b) -> (sig b -> b) -> (Free sig a -> b)
fold gen alg (Var x) = gen x
fold gen alg (Op op) = alg (fmap (fold gen alg) op)

genS :: a -> (s -> a)
genS x = \ s -> x

algS :: (STATE s) (s -> a) -> (s -> a)
algS (GET k) = \ s -> k s s
algS (PUT s k) = \ _ -> k () s

exec3 = fold genS algS (incr' >> get') 5

--- 3.2 Modular Algebraic Effects

data (sig1 + sig2) a 
  = Inl (sig1 a) 
  | Inr (sig2 a)
  deriving Functor

data VOID k deriving Functor

runVOID :: Free VOID a -> a
runVOID = fold id undefined

(▽) :: (sig1 b -> b) -> (sig2 b -> b) -> ((sig1 + sig2) b -> b)
(alg1 ▽ alg2) (Inl op) = alg1 op
(alg1 ▽ alg2) (Inr op) = alg2 op


data FAIL k = FAIL
  deriving Functor
fail' = Op FAIL

type CF a = Free (STATE Int + VOID) (Maybe a)

genMF :: Monad m => a -> CF a
genMF x = return (Just x)

algMF :: FAIL (CF a) -> (CF a)
algMF FAIL = return Nothing

fwdMF ::  (STATE Int + VOID) (CF a) -> (CF a)
fwdMF op = Op op

handleMF :: Free (FAIL + (STATE Int + VOID)) a -> Free (STATE Int + VOID) (Maybe a)
handleMF = fold genMF (algMF ▽ fwdMF)