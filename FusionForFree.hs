{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TypeOperators #-}
module FusionForFree where


--- 2 Algebraic Effect Handlers

data Free f a where
  Var :: a -> Free f a
  Con :: f (Free f a) -> Free f a
  deriving (Functor, Applicative)

fold :: Functor f => (f b -> b) -> (a -> b) -> (Free f a -> b)
fold alg gen (Var x ) = gen x
fold alg gen (Con op) = alg (fmap (fold alg gen) op)

instance Functor f => Monad (Free f ) where
  return x = Var x
  m >>= f = fold Con f m


--- 2.1 Nondeterminsm

data Nondet k where
  Or :: k -> k -> Nondet k

instance Functor Nondet where
  fmap f (Or x y) = Or (f x ) (f y)

coin :: Free Nondet Bool
coin = Con (Or (Var True) (Var False))

handleNondetL  :: Free Nondet a -> [a ]
handleNondetL  = fold algNondetL genNondetL

algNondetL :: Nondet [a] -> [a]
algNondetL (Or l1 l2) = l1 ++ l2
genNondetL :: a -> [a ]
genNondetL x = [x]

testCoin :: [Bool]
testCoin = handleNondetL coin


--- 2.2 Handler Composition

data (+) f g a where
  Inl :: f a -> (f + g) a
  Inr :: g a -> (f + g) a
instance (Functor f , Functor g) => Functor (f + g) where
  fmap f (Inl s) = Inl (fmap f s)
  fmap f (Inr s) = Inr (fmap f s)



handleNondet :: Functor g => Free (Nondet + g) a -> Free g [a ]
handleNondet = fold (algNondet ▽ Con) genNondet

genNondet :: Functor g => a -> Free g [a ]
genNondet x = Var [x ]

algNondet :: Functor g => Nondet (Free g [a ]) -> Free g [a ]
algNondet (Or ml1 ml2) =
  do {l1 <- ml1 ; l2 <- ml2 ; Var (l1 ++ l2)}

(▽) :: (f b -> b) -> (g b -> b) -> ((f + g) b -> b)
(▽) algf algg (Inl s) = algf s
(▽) algf algg (Inr s) = algg s