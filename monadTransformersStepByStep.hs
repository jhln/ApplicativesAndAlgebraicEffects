{-# LANGUAGE GADTs #-}

--- source code : https://github.com/metadave/monad-transformers-step-by-step

module MonadTransformersStepByStep where

import qualified Data.Map as Map
import           Data.Maybe
import           Control.Monad.Identity
import qualified Control.Monad.Fail     as Fail
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Writer



type Name = String

data Exp
    = Lit Integer
    | Var Name
    | Plus Exp
           Exp
    | Abs Name
          Exp
    | App Exp
          Exp
    deriving (Show, Eq)

data Value
    = IntVal Integer
    | FunVal Env
             Name
             Exp
    deriving (Show, Eq)

type Env = Map.Map Name Value

exampleExp :: Exp
exampleExp = 
  Lit 12 `Plus` (App (Abs "x" (Var "x")) (Lit 4 `Plus` Lit 2))

--- 1.1 Example Program

eval0 :: Env -> Exp -> Value
eval0 env (Lit i) = IntVal i
eval0 env (Var n) = fromJust (Map.lookup n env)
eval0 env (Plus e1 e2) = let IntVal i1 = eval0 env e1
                             IntVal i2 = eval0 env e2
                         in IntVal (i1 + i2)
eval0 env (Abs n e) = FunVal env n e
eval0 env (App e1 e2) = let val1 = eval0 env e1
                            val2 = eval0 env e2
                         in case val1 of
                            FunVal env' n body -> eval0 (Map.insert n val2 env') body

execEval0 = eval0 Map.empty exampleExp


--- 2 Monad Transformers
--- 2.1 Converting to Monadic Style

instance Fail.MonadFail Identity where
  fail = Fail.fail

type Eval1 a = Identity a

runEval1 :: Eval1 a -> a
runEval1 = runIdentity


eval1 :: Env -> Exp -> Eval1 Value
eval1 env (Lit i) = return $ IntVal i
eval1 env (Var n) = 
  maybe 
    (error ("undefined variable: " ++ n)) 
    return $ Map.lookup n env
eval1 env (Plus e1 e2) = do
                            IntVal i1 <- eval1 env e1
                            IntVal i2 <- eval1 env e2
                            return $ IntVal (i1 + i2)
eval1 env (Abs n e) = return $ FunVal env n e
eval1 env (App e1 e2) = do val1 <- eval1 env e1
                           val2 <- eval1 env e2
                           case val1 of
                              FunVal env' n body -> 
                                eval1 
                                  (Map.insert n val2 env') 
                                  body

execEval1 = runEval1 (eval1 Map.empty exampleExp)


--- 2.2 Adding Error Handling

type Eval2 a = ExceptT String Identity a

runEval2 :: Eval2 a -> Either String a
runEval2 ev  = runIdentity (runExceptT ev)

eval2a                   ::  Env -> Exp -> Eval2 Value
eval2a env (Lit i)       =   return $ IntVal i
eval2a env (Var n)       =   maybe (error ("undefined variable: " ++ n)) return $ Map.lookup n env
eval2a env (Plus e1 e2)  =   do  IntVal i1  <- eval2a env e1
                                 IntVal i2  <- eval2a env e2
                                 return $ IntVal (i1 + i2)
eval2a env (Abs n e)     =   return $ FunVal env n e
eval2a env (App e1 e2)   =   do  val1  <- eval2a env e1
                                 val2  <- eval2a env e2
                                 case val1 of
                                    FunVal env' n body ->
                                       eval2a (Map.insert n val2 env') body

execEval2a = runEval2 (eval2a Map.empty exampleExp)


eval2b                   ::  Env -> Exp -> Eval2 Value
eval2b _   (Lit i)       =   return $ IntVal i
eval2b env (Var n)       =   maybe (error ("undefined variable: " ++ n)) return $ Map.lookup n env
eval2b env (Plus e1 e2)  =   do  e1'  <- eval2b env e1
                                 e2'  <- eval2b env e2
                                 case (e1', e2') of
                                   (IntVal i1, IntVal i2) ->
                                       return $ IntVal (i1 + i2)
                                   _ -> throwError "type error"
eval2b env (Abs n e)     =   return $ FunVal env n e
eval2b env (App e1 e2)   =   do  val1  <- eval2b env e1
                                 val2  <- eval2b env e2
                                 case val1 of
                                    FunVal env' n body ->
                                       eval2b (Map.insert n val2 env') body
                                    _ -> throwError "type error"


execEval2b = runEval2 (eval2b Map.empty exampleExp)

exampleErrorExp :: Exp
exampleErrorExp = (Plus (Lit 1) (Abs "x" (Var "x")))

execEvalError2b = runEval2 (eval2b Map.empty exampleErrorExp)
-- t1 = runEval2 (eval2b Map.empty (Var "x"))

eval2c                   ::  Env -> Exp -> Eval2 Value
eval2c env (Lit i)       =   return $ IntVal i
eval2c env (Var n)       =   maybe (error ("undefined variable: " ++ n)) return $ Map.lookup n env
eval2c env (Plus e1 e2)  =   do  IntVal i1  <- eval2c env e1
                                 IntVal i2  <- eval2c env e2
                                 return $ IntVal (i1 + i2)
eval2c env (Abs n e)     =   return $ FunVal env n e
eval2c env (App e1 e2)   =   do  FunVal env' n body  <- eval2c env e1
                                 val2                <- eval2c env e2
                                 eval2c (Map.insert n val2 env') body

execEval2c = runEval2 (eval2c Map.empty exampleExp)
execEval2cError = runEval2 (eval2c Map.empty exampleErrorExp)


eval2                    ::  Env -> Exp -> Eval2 Value
eval2  env (Lit i)       =   return $ IntVal i
eval2  env (Var n)       =   case Map.lookup n env of
                               Nothing -> throwError ("unbound variable: " ++ n)
                               Just val -> return val
eval2  env (Plus e1 e2)  =   do  e1'  <- eval2  env e1
                                 e2'  <- eval2  env e2
                                 case (e1', e2') of
                                   (IntVal i1, IntVal i2) ->
                                       return $ IntVal (i1 + i2)
                                   _ -> throwError "type error in addition"
eval2  env (Abs n e)     =   return $ FunVal env n e
eval2  env (App e1 e2)   =   do  val1  <- eval2  env e1
                                 val2  <- eval2  env e2
                                 case val1 of
                                    FunVal env' n body ->
                                       eval2  (Map.insert n val2 env') body
                                    _ -> throwError "type error in application"

execEval2 = runEval2 (eval2 Map.empty exampleExp)
execEval2Error = runEval2 (eval2 Map.empty exampleErrorExp)


--- 2.3 Hiding the Environment

type Eval3 a = ReaderT Env (ExceptT String Identity) a

runEval3     :: Env -> Eval3 a -> Either String a
runEval3 env ev  = runIdentity (runExceptT (runReaderT ev env))


eval3               ::  Exp -> Eval3 Value
eval3 (Lit i)       =   return $ IntVal i
eval3 (Var n)       =   do  env <- ask
                            case Map.lookup n env of
                               Nothing -> throwError ("unbound variable: " ++ n)
                               Just val -> return val
eval3 (Plus e1 e2)  =   do  e1'  <- eval3 e1
                            e2'  <- eval3 e2
                            case (e1', e2') of
                              (IntVal i1, IntVal i2) ->
                                  return $ IntVal (i1 + i2)
                              _ -> throwError "type error in addition"
eval3 (Abs n e)     =   do  env <- ask
                            return $ FunVal env n e
eval3 (App e1 e2)   =   do  val1  <- eval3 e1
                            val2  <- eval3 e2
                            case val1 of
                               FunVal env' n body ->
                                  local (const (Map.insert n val2 env'))
                                    (eval3 body)
                               _ -> throwError "type error in application"

execEval3 = runEval3 Map.empty (eval3 exampleExp)
execEval3Error = runEval3 Map.empty (eval3 exampleErrorExp)


--- 2.4 Adding State

type Eval4 a = ReaderT Env (ExceptT String (StateT Integer Identity)) a

runEval4            ::  Env -> Integer -> Eval4 a -> (Either String a, Integer)
runEval4 env st ev  =   runIdentity (runStateT (runExceptT (runReaderT ev env)) st)


tick :: (Num s, MonadState s m) => m ()
tick = do  st <- get
           put (st + 1)


eval4               ::  Exp -> Eval4 Value
eval4 (Lit i)       =   do  tick
                            return $ IntVal i
eval4 (Var n)       =   do  tick
                            env <- ask
                            case Map.lookup n env of
                               Nothing -> throwError ("unbound variable: " ++ n)
                               Just val -> return val
eval4 (Plus e1 e2)  =   do  tick
                            e1'  <- eval4 e1
                            e2'  <- eval4 e2
                            case (e1', e2') of
                              (IntVal i1, IntVal i2) ->
                                  return $ IntVal (i1 + i2)
                              _ -> throwError "type error in addition"
eval4 (Abs n e)     =   do  tick
                            env <- ask
                            return $ FunVal env n e
eval4 (App e1 e2)   =   do  tick
                            val1  <- eval4 e1
                            val2  <- eval4 e2
                            case val1 of
                               FunVal env' n body ->
                                  local (const (Map.insert n val2 env'))
                                    (eval4 body)
                               _ -> throwError "type error in application"

execEval4 = runEval4 Map.empty 0 (eval4 exampleExp)


--- 2.5 Adding Logging

type Eval5 a 
  = ReaderT 
      Env  
      (ExceptT 
        String
        (WriterT [String] (StateT Integer Identity))) 
      a

runEval5 ::  Env -> Integer -> Eval5 a -> ((Either String a, [String]), Integer)
runEval5 env st ev  =
    runIdentity 
      (runStateT 
        (runWriterT 
          (runExceptT 
            (runReaderT ev env))) 
      st)

eval5               ::  Exp -> Eval5 Value
eval5 (Lit i)       =   do  tick
                            return $ IntVal i
eval5 (Var n)       =   do  tick
                            tell [n]
                            env <- ask
                            case Map.lookup n env of
                               Nothing -> throwError ("unbound variable: " ++ n)
                               Just val -> return val
eval5 (Plus e1 e2)  =   do  tick
                            e1'  <- eval5 e1
                            e2'  <- eval5 e2
                            case (e1', e2') of
                              (IntVal i1, IntVal i2) ->
                                  return $ IntVal (i1 + i2)
                              _ -> throwError "type error in addition"
eval5 (Abs n e)     =   do  tick
                            env <- ask
                            return $ FunVal env n e
eval5 (App e1 e2)   =   do  tick
                            val1  <- eval5 e1
                            val2  <- eval5 e2
                            case val1 of
                               FunVal env' n body ->
                                  local (const (Map.insert n val2 env'))
                                    (eval5 body)
                               _ -> throwError "type error in application"

execEval5 = runEval5 Map.empty 0 (eval5 exampleExp)



--- 2.6 What about I/O?

type Eval a 
  = ReaderT 
      Env 
      (ExceptT 
        String
        (WriterT [String] (StateT Integer IO))) 
      a


runEval6 :: Env -> Integer -> Eval a -> IO ((Either String a, [String]), Integer)
runEval6 env st ev =
    runStateT (runWriterT $ runExceptT $ runReaderT ev env) st

eval6 :: Exp -> Eval Value
eval6 (Lit i) = do
    tick
    liftIO $ print i
    return $ IntVal i
eval6 (Var n) = do
    tick
    tell [n]
    env <- ask
    case Map.lookup n env of
        Just n' -> return n'
        Nothing -> throwError ("undefined variable: " ++ n)
eval6 (Plus a b) = do
    tick
    ia <- eval6 a
    ib <- eval6 b
    case (ia, ib) of
        (IntVal a', IntVal b') -> return $ IntVal (a' + b')
        _                      -> throwError "type error in addition"
eval6 (Abs n e) = do
    tick
    env <- ask
    return $ FunVal env n e
eval6 (App a b) = do
    tick
    a' <- eval6 a
    b' <- eval6 b
    case a' of
      FunVal env' n body -> local (const $ Map.insert n b' env') (eval6 body)
      _                  -> throwError "type error in application"

execEval6 = runEval6 Map.empty 0 (eval6 exampleExp)
