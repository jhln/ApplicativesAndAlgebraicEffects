{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module EffectHandlersEvidently where

import Control.Ev.Eff hiding 
  (local, handlerHide, handlerLocal, Local, lget, lput)


data Reader a e ans
  = Reader{ ask :: Op () a e ans }

greet :: (Reader String :? e) => Eff e String
greet = do 
          s <- perform ask ()
          return ("hello " ++ s)

reader :: Eff (Reader String :* e) ans -> Eff e ans
reader action
  = handler (Reader{ ask = value "world" }) action

helloWorld :: Eff e String
helloWorld = reader greet

test :: String
test = runEff helloWorld


--- 4 Examples
--- 4.1 Exception

data Exn e ans
  = Exn { failure :: forall a. Op () a e ans }

safeDiv :: (Exn :? e) => Int -> Int -> Eff e Int
safeDiv x 0 = perform failure ()
safeDiv x y = return (div x y)

toMaybe :: Eff (Exn :* e) a -> Eff e (Maybe a)
toMaybe = 
  handlerRet 
    Just 
    $ Exn{ failure = operation (\ () _ -> return Nothing) }

test2 = runEff (toMaybe $ safeDiv 42 2)
test3 = runEff (toMaybe $ safeDiv 42 0)


exceptDefault :: a -> Eff (Exn :* e) a -> Eff e a
exceptDefault x = 
  handler 
  $ Exn{ failure = operation (\ () _ -> return x) }


test4 = runEff (exceptDefault 0 $ safeDiv 42 2)
test5 = runEff (exceptDefault 0 $ safeDiv 42 0)


--- 4.2 State

data State a e ans = 
  State { get :: Op () a e ans
        , put :: Op a () e ans }


invert :: (State Bool :? e) => Eff e Bool
invert = do 
          b <- perform get ()
          perform put (not b)
          perform get ()


state :: a -> Eff (State a :* e) ans -> Eff e ans
state init = 
  handlerLocal init 
  $ State { get = function (\ () -> perform lget ())
          , put = function (\ x -> perform lput x) }

test6 = runEff (state True invert)


--- 4.3 State as a Function

data Local a e ans = Local{ lget :: Op () a e ans, lput :: Op a () e ans }

local :: a -> Eff (Local a :* e) ans -> Eff e ans
local init action = 
  do 
    f <- handler (Local{
                    lget = operation (\ () k -> 
                                return 
                                $ \s -> do{ r <- k s; r s } )
                    ,lput = operation (\ s k -> return $
                              \_ -> do{ r <- k (); r s } )
        })
        (do x <- action
            return (\s -> return x))
    f init


handlerLocal :: a => 
  (h (Local a :* e) ans) -> Eff (h :* e) ans -> Eff e ans
handlerLocal init h action = 
  local init (handlerHide h action)

handlerHide :: 
  h (h0 :* e) ans -> Eff (h :* e) ans -> Eff (h0 :* e) ans
handlerHide = undefined