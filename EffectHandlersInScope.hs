{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverlappingInstances #-}



module EffectHandlersInScope where

import Control.Monad


--- 2. Backtracking Computation


data Backtr a
  = ReturnB a
  | FailB
  | (Backtr a) :|| (Backtr a)
  deriving Show

instance Functor Backtr where
  fmap f s = s >>= ReturnB . f

instance Applicative Backtr where
  pure = ReturnB
  f' <*> s' = do { f <- f'; s <- s'; ReturnB $ f s}

instance Monad Backtr where
  return a = ReturnB a
  ReturnB a >>= r = r a
  FailB >>= r = FailB
  (p :|| q) >>= r = (p>>=r) :|| (q>>=r)

knapsack ::Int -> [Int] -> Backtr [Int]
knapsack w vs 
  | w < 0 = FailB
  | w == 0 = ReturnB []
  | w > 0 = do 
              v <- select vs
              vs' <- knapsack (w - v) vs 
              ReturnB (v : vs')

select :: [a] -> Backtr a
select = foldr (:||) FailB . (map ReturnB)

test1 :: Backtr [Int]
test1 = knapsack 3 [1,2]
test2 :: Backtr [Int]
test2 = knapsack 3 [3,2,1]

allsolsB::Backtr a -> [a]
allsolsB (ReturnB a) = [a]
allsolsB (FailB) = []
allsolsB (p :|| q) = allsolsB p ++ allsolsB q

test3 :: [[Int]]
test3 = allsolsB $ knapsack 3 [3,2,1]



--- 3. Syntax Signatures



data Prog sig a
  = Return a                -- pure computations
  | Op (sig (Prog sig a))   -- impure computations
  deriving (Functor, Applicative)

instance (Functor sig) => Monad (Prog sig) where
  return v = Return v
  Return v >>= prog = prog v
  Op op >>= prog = Op (fmap (>>= prog) op)

data Nondet cnt
  = Fail'
  | cnt :| cnt
  deriving Functor

data (sig1 + sig2) cnt = Inl (sig1 cnt) | Inr (sig2 cnt)
  deriving Functor


class (Functor sub,Functor sup) => sub ⊂ sup where
  inj :: sub a -> sup a
  prj :: sup a -> Maybe (sub a)
instance Functor sig => sig ⊂ sig where
  inj = id
  prj = Just

instance (Functor sig1, Functor sig2) 
  => sig1 ⊂ (sig1 + sig2) where
  inj = Inl
  prj (Inl fa) = Just fa
  prj _ = Nothing
instance (Functor sig1, sig ⊂ sig2) 
  => sig ⊂ (sig1 + sig2) where
  inj = Inr . inj
  prj (Inr ga) = prj ga
  prj _ = Nothing

inject ::(sub ⊂ sup) => sub (Prog sup a) -> Prog sup a
inject = Op . inj

project ::(sub ⊂ sup) => Prog sup a -> Maybe (sub (Prog sup a))
project (Op s)  = prj s
project _       = Nothing

pattern Fail <- (project -> Just Fail')
fail ::(Nondet ⊂ sig) => Prog sig a
fail = inject Fail'

pattern Choice p q <- (project -> Just (p :| q))
choice :: (Nondet ⊂ sig) => Prog sig a -> Prog sig a -> Prog sig a
choice p q = inject (p :| q)

data Void cnt 
  deriving Functor

run ::Prog Void a -> a
run (Return x) = x

pattern Other s = Op (Inr s) 

solutions::(Functor sig) => Prog (Nondet + sig) a -> Prog sig [a]
solutions (Return a) = return [a]
solutions (Fail) = return []
solutions (Choice p q) = liftM2 (++) (solutions p) (solutions q)
solutions (Other op) = Op (fmap solutions op)

allsols::Prog (Nondet + Void) a -> [a]
allsols = run . solutions


data State s cnt
  = Get' (s -> cnt)
  | Put' s cnt
  deriving Functor

pattern Get k <- (project -> Just (Get' k))
get ::(State s ⊂ sig) => Prog sig s
get = inject (Get' return)

pattern Put s k <- (project -> Just (Put' s k))
put ::(State s ⊂ sig) => s -> Prog sig ()
put s = inject (Put' s (return ()))

runState ::Functor sig 
  => s -> Prog (State s + sig) a -> Prog sig (s,a)
runState s (Return a) = return (s,a)
runState s (Get k) = runState s (k s)
runState s (Put s' k) = runState s' k
runState s (Other op) = Op (fmap (runState s) op)