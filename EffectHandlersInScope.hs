{-# LANGUAGE DeriveFunctor #-}

module EffectHandlersInScope where

data Backtr a
  = Return a
  | Fail
  | Backtr a :|| Backtr a


instance Functor Backtr where
  fmap f s = s >>= return . f

instance Applicative Backtr where
  pure = return
  f' <*> s' = do { f <- f'; s <- s'; return $ f s}

instance Monad Backtr where
  return a = Return a
  Return a >>= r = r a
  Fail >>= r = Fail
  (p :|| q) >>= r = (p>>=r) :|| (q>>=r)

