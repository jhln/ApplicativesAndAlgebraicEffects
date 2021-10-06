{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
module SyntaxAndSemanticsForOperationsWithScopes where

import Prelude hiding (or)

data Prog f g a 
  = Var a
  | Op (f (Prog f g a))
  | Scope (g (Prog f g (Prog f g a)))
  deriving (Functor, Applicative)

instance (Functor f , Functor g) => Monad (Prog f g) where
  return = Var
  Var x >>= f = f x
  Op op >>= f = Op (fmap (>>=f ) op)
  Scope sc >>= f = Scope (fmap (fmap (>>=f )) sc)

data Choice a 
  = Fail 
  | Or a a 
  deriving Functor
data Once a = Once a 
  deriving Functor
type NDProg = Prog Choice Once

example4 :: NDProg Int
example4 = do 
  x <- once (or (return 1) (return 5))
  or (return x) (return (x + 1))

fail :: NDProg a
fail = Op Fail
or :: NDProg a -> NDProg a -> NDProg a
or x y = Op (Or x y)
once :: NDProg a -> NDProg a
once x = Scope (Once (fmap return x))

data Nat 
  = Zero 
  | Succ Nat
data Alg f g a 
  = A { a :: forall n. f (a n) -> a n
      , d :: forall n. g (a (Succ n)) -> a n
      , p :: forall n. a n -> a (Succ n)}

fold :: (Functor f , Functor g) 
  => Alg f g a -> Prog f g (a n) -> a n
fold alg (Var x) = x
fold alg (Op op) = a alg (fmap (fold alg) op)
fold alg (Scope sc) = 
  d alg (fmap (fold alg . fmap (p alg . fold alg)) sc)

run :: (Functor f , Functor g)
  => (r -> a Zero) -> Alg f g a -> (Prog f g r -> a Zero)
run gen alg prog = fold alg (fmap gen prog)

data CarrierND a n = ND [CarrierND' a n]
data CarrierND' a :: Nat -> * where
  CZND :: a -> CarrierND' a Zero
  CSND :: [CarrierND' a n] -> CarrierND' a (Succ n)

genND :: a -> CarrierND a Zero
genND x = ND [CZND x ]
algND :: Alg Choice Once (CarrierND a)
algND = A {..} 
  where
    a :: forall n a. Choice (CarrierND a n) -> CarrierND a n
    a Fail = ND []
    a (Or (ND l) (ND r)) = ND (l ++ r)
    d :: forall n a. Once (CarrierND a (Succ n)) -> CarrierND a n
    d (Once (ND [])) = ND []
    d (Once (ND (CSND l:_))) = ND l
    p :: forall n a. CarrierND a n -> CarrierND a (Succ n)
    p (ND l) = ND [CSND l]

main :: [Int]
main = toList (run genND algND example4) 
  where
    toList :: CarrierND a Zero -> [a]
    toList (ND l) = map (\(CZND x) -> x) l


--- 7 Examples 

--- 7. a) state with local variables

type Name = String
data State s a 
  = Get Name (s -> a) 
  | Put Name s a 
  deriving Functor
data Local s a 
  = Local Name s a 
  deriving Functor
type LSProg s = Prog (State s) (Local s)

get :: Name -> LSProg s s
get x = Op (Get x (\ s -> return s))
put :: Name -> s -> LSProg s ()
put x s = Op (Put x s (return ()))
local :: Name -> s -> LSProg s a -> LSProg s a
local x s p = Scope (fmap (fmap return) (Local x s p))

type Memory s = Name -> Maybe s
retrieve :: Name -> Memory s -> s
retrieve x m = 
  case m x of 
    Just s -> s
    Nothing -> error ("var undefined")
update :: Name -> s -> Memory s -> Memory s
update x s m y 
  | x == y    = Just s
  | otherwise = m y

data CarrierLS s a n =
  LS {runLS :: (Memory s -> (CarrierLS' s a n, Memory s))}
data CarrierLS' s a :: Nat -> * 
  where
    CZLS :: a -> CarrierLS' s a Zero
    CSLS :: (Memory s -> (CarrierLS' s a n, Memory s)) -> CarrierLS' s a (Succ n)

genLS :: a -> CarrierLS s a Zero
genLS a = LS ( \ m -> (CZLS a, m))
algLS :: Alg (State s) (Local s) (CarrierLS s a)
algLS = A {..} 
  where
    a (Put x s (LS f )) = LS (f . update x s)
    a (Get x p) = LS (\ m -> runLS (p (retrieve x m)) m)
    d :: forall s n a. Local s (CarrierLS s a (Succ n)) -> CarrierLS s a n
    d (Local x s (LS f )) 
      = LS (\ m -> 
          case f (update x s m) of
            (CSLS g, n) -> g (update x (retrieve x m) n))
    p :: forall s n a. CarrierLS s a n -> CarrierLS s a (Succ n)
    p l = LS (\ m -> (CSLS (runLS l), m))

testLS :: LSProg s a -> a
testLS p 
  = case fst (runLS (run genLS algLS p) (\ x -> Nothing)) of
      CZLS a -> a

incr :: Name -> Int -> LSProg Int ()
incr x i = do
  v <- get x
  put x (v + i)

testProgLS :: LSProg Int (Int, Int)
testProgLS = do 
  put "x" 1
  put "y" 1
  local "x" 100 (do 
                  incr "x" 100
                  v <- get "x"
                  incr "y" v)
  incr "x" 2
  incr "y" 2
  vx <- get "x"
  vy <- get "y"
  return (vx, vy)

localVarTest = testLS testProgLS


--- 7. b) concurrency via resumptions

data Act m a 
  = Act (m a) 
  | Kill 
  deriving Functor
data Con a 
  = Spawn a a 
  | Atomic a 
  deriving Functor
type ConProg m = Prog (Act m) Con

lift :: Functor m => m a -> ConProg m a
lift m = Op (Act (fmap return m))
kill :: ConProg m a
kill = Op Kill

spawn :: Functor m 
  => ConProg m a -> ConProg m b -> ConProg m a
spawn p q = Scope (fmap (fmap return) (Spawn p (q >> kill)))
atomic :: Functor m 
  => ConProg m a -> ConProg m a
atomic p = Scope (fmap (fmap return) (Atomic p))

data Resumption m a 
  = More (m (Resumption m a)) 
  | Done a
  deriving Functor

retraction :: Monad m => Resumption m a -> m a
retraction (More m) = m >>= retraction
retraction (Done a) = return a

interleaveL :: Functor m 
  => Resumption m a -> Resumption m b -> Resumption m a
interleaveL (Done a) r = fmap (\ _ -> a) r
interleaveL r (Done _) = r
interleaveL (More m) (More m') =
  More (fmap (\ r -> More (fmap (\ r' -> interleaveL r r') m')) m)

data CarrierCon m a n =
  CC {runCC :: Resumption m (CarrierCon' m a n)}
data CarrierCon' m a :: Nat -> * 
  where
    CZCC :: a -> CarrierCon' m a Zero
    CSCC :: Resumption m (CarrierCon' m a n) -> CarrierCon' m a (Succ n)

rJoin :: Functor m 
  => Resumption m (CarrierCon' m a (Succ n)) -> Resumption m (CarrierCon' m a n)
rJoin (Done (CSCC r)) = r
rJoin (More m) = More (fmap rJoin m)

genCC :: Monad m => a -> CarrierCon m a Zero
genCC a = CC (Done (CZCC a))

algCC :: Monad m => Alg (Act m) Con (CarrierCon m a)
algCC = A {..} 
  where
    a (Act m) = CC (More (fmap runCC m))
    a (Kill) = CC (Done (error "main process killed"))
    d :: forall m n a. Monad m 
      => Con (CarrierCon m a (Succ n)) -> CarrierCon m a n
    d (Atomic (CC r)) =
      CC (More (fmap (\ (CSCC s) -> s) (retraction r)))
    d (Spawn (CC r) (CC r')) = CC (rJoin (interleaveL r r'))
    p :: forall m n a. CarrierCon m a n -> CarrierCon m a (Succ n)
    p (CC r) = CC (Done (CSCC r))

runCon :: Monad m => ConProg m a -> m a
runCon p = retraction 
  (fmap (\ (CZCC a) -> a) (runCC (run genCC algCC p)))

say :: String -> ConProg IO ()
say = lift . putStr

conTest1 :: ConProg IO ()
conTest1 = do
  spawn 
    (say "hello " >> say "world ")
    (say "goodbye " >> say "cruel " >> say "world ")
conTest2 :: ConProg IO ()
conTest2 = do
  --(mapM say ["-", "-", "-"])
  return ()

runConTest1 = runCon conTest1
runConTest2 = runCon conTest2