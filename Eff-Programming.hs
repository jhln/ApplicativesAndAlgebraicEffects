module Eff where


data STDType a b
  = Ints
  | Bools
  | Unity
  | Emptness
  | Prod a b
  | Sum a b
  | Func a b
  | Eff (Effect a b)
  | Handler a b

data Effect a b
  = Effect Op Int a b

newtype Op = Op String
newtype Var = Var String

data Expression e1 e2
  = VarE Var
  | IntE Int
  | ConstE Int
  | UnityE
  | ProdE e1 e2
  | Left String
  | Right String
  | Fun  (STDType e1 e2) (Expression e1 e2)

data Computation
  = Val (Expression )
  | Let Var Computation Computation