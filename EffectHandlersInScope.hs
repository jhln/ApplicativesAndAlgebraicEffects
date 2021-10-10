{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverlappingInstances #-}



module EffectHandlersInScope where

import Control.Monad hiding (fail)
import Prelude hiding (fail)


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

knapsackB :: Int -> [Int] -> Backtr [Int]
knapsackB w vs 
  | w < 0 = FailB
  | w == 0 = ReturnB []
  | w > 0 = do 
              v <- selectB vs
              vs' <- knapsackB (w - v) vs 
              ReturnB (v : vs')

selectB :: [a] -> Backtr a
selectB = foldr (:||) FailB . (map ReturnB)

test1 :: Backtr [Int]
test1 = knapsackB 3 [1,2]
test2 :: Backtr [Int]
test2 = knapsackB 3 [3,2,1]

allsolsB::Backtr a -> [a]
allsolsB (ReturnB a) = [a]
allsolsB (FailB) = []
allsolsB (p :|| q) = allsolsB p ++ allsolsB q

test3 :: [[Int]]
test3 = allsolsB $ knapsackB 3 [3,2,1]



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

inject :: (sub ⊂ sup) => sub (Prog sup a) -> Prog sup a
inject = Op . inj

project :: (sub ⊂ sup) => Prog sup a -> Maybe (sub (Prog sup a))
project (Op s)  = prj s
project _       = Nothing

pattern Fail <- (project -> Just Fail')
fail :: (Nondet ⊂ sig) => Prog sig a
fail = inject Fail'

pattern Choice p q <- (project -> Just (p :| q))
choice :: (Nondet ⊂ sig) => Prog sig a -> Prog sig a -> Prog sig a
choice p q = inject (p :| q)

data Void cnt 
  deriving Functor

run :: Prog Void a -> a
run (Return x) = x

pattern Other s = Op (Inr s) 

solutions :: (Functor sig) => Prog (Nondet + sig) a -> Prog sig [a]
solutions (Return a) = return [a]
solutions (Fail) = return []
solutions (Choice p q) = liftM2 (++) (solutions p) (solutions q)
solutions (Other op) = Op (fmap solutions op)

allsols :: Prog (Nondet + Void) a -> [a]
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

--runLocal :: Functor sig => 
--  s -> Prog (State s + Nondet + sig) a -> Prog sig [(s,a)]
runLocal :: Functor sig =>
     s -> Prog (State s + (Nondet + sig)) a -> Prog sig [(s, a)]
runLocal s = solutions . (runState s)

--runGlobal :: Functor sig =>
--  s -> Prog (Nondet + State s + sig) a -> Prog sig (s,[a])
runGlobal :: Functor sig =>
     s -> Prog (Nondet + (State s + sig)) a -> Prog sig (s, [a])
runGlobal s = (runState s) . solutions

choices :: (Nondet ⊂ sig,State Int ⊂ sig) => 
  Prog sig a -> Prog sig a
choices (Return a) = return a
choices (Fail) = fail
choices (Choice p q) = incr >>(choice (choices p) (choices q))
choices (Op op) = Op (fmap choices op)

incr::(State Int ⊂ sig) => Prog sig ()
incr = get >>= put . (succ :: Int -> Int)

knapsack :: (Nondet ⊂ sig) => Int -> [Int] -> Prog sig [Int]

knapsack w vs 
  | w < 0 = fail
  | w == 0 = Return []
  | w > 0 = do 
              v <- select vs
              vs' <- knapsack (w - v) vs 
              Return (v : vs')

select ::(Nondet ⊂ sig) => [a] -> Prog sig a
select = foldr choice fail . (map Return)

testGlobal :: (Int, [[Int]])
testGlobal = (run . runGlobal (0 ::Int) . choices) (knapsack 3 [3,2,1])
testLocal :: [(Int, [Int])]
testLocal = (run . runLocal (0 ::Int) . choices) (knapsack 3 [3,2,1])



--- 5. Cut and Call


data Cut cnt = Cutfail'
  deriving Functor
pattern Cutfail <- (project -> Just Cutfail')
cutfail :: (Cut ⊂ sig) => Prog sig a
cutfail = inject Cutfail'


call ::(Nondet ⊂ sig) => Prog (Cut + sig) a -> Prog sig a
call p = go p fail where
  go :: (Nondet ⊂ sig) =>
    Prog (Cut + sig) a -> Prog sig a -> Prog sig a
  go (Return a) q = choice (return a) q
  go (Fail) q = q
  go (Cutfail) q = fail
  go (Choice p1 p2) q = go p1 (go p2 q)
  go (Other op) q = Op (fmap (flip go q) op)


cut ::(Nondet ⊂ sig,Cut ⊂ sig) => Prog sig ()
cut = choice skip cutfail
skip ::Monad m => m ()
skip = return ()


once ::(Nondet ⊂ sig) => Prog (Cut + sig) b -> Prog sig b
once p = call (do x <- p; cut; return x)

testOnce :: [[Int]]
testOnce = (run . solutions . once) (knapsack 3 [3,2,1])


--- 6. Grammars


data Symbol cnt = Symbol' Char (Char -> cnt)
  deriving Functor
symbol :: (Symbol ⊂ sig) => Char -> Prog sig Char
symbol c = inject (Symbol' c return)

digit :: (Nondet ⊂ sig,Symbol ⊂ sig) => Prog sig Char
digit = foldr choice fail (fmap symbol ['0' .. '9'])


many,many1 ::(Nondet ⊂ sig) => Prog sig a -> Prog sig [a]
many p = choice (many1 p) (return [])
many1 p = do 
            a <- p
            as <- many p
            return (a : as)


parse ::(Nondet ⊂ sig) =>
  [Char] -> Prog (Symbol + sig) a -> Prog sig a
parse [] (Return a) = return a
parse (x : xs) (Return a) = fail
parse [] (Op (Inl (Symbol' c k))) = fail
parse (x : xs) (Op (Inl (Symbol' c k)))
  | x == c       = parse xs (k x)
  | otherwise = fail
parse xs (Other op) = Op (fmap (parse xs) op)


expr::(Nondet ⊂ sig, Symbol ⊂ sig) => Prog sig Int
expr = choice
        (do i <- term; symbol '+'; j <- expr; return (i+j))
        (do i <- term; return i)
term :: (Nondet ⊂ sig,Symbol ⊂ sig) => Prog sig Int
term = 
  choice
  do i <- factor; symbol '*'; j <- term; return (i * j)
  do i <- factor; return i

factor :: (Nondet ⊂ sig,Symbol ⊂ sig) => Prog sig Int
factor = 
  choice
  do ds <- many1 digit; return (read ds)
  do symbol '('; i <- expr; symbol ')'; return i

testParse :: [Int]
testParse = (allsols . parse "2+8*5") expr

expr1 ::(Nondet ⊂ sig,Symbol ⊂ sig) => Prog sig Int
expr1 = do 
          i <- term
          choice
            do symbol '+'; j <- expr1; return (i + j)
            do return i

expr2 :: (Nondet ⊂ sig,Symbol ⊂ sig) => Prog sig Int
expr2 = do 
          i <- term
          call 
            (choice
              do symbol '+'; cut; j <- expr2; return (i+j)
              do return i)