-- | Program to test parser.
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Interpreter(execProgram) where

import Prelude
import System.Environment ( getArgs )
import System.Exit
import Control.Monad      ( when )
import Utils

import AbsLatteFun
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Char


maybeHead :: [a] -> Maybe a
maybeHead (x:_) = Just x
maybeHead _ = Nothing

newloc :: Store -> Loc
newloc store = (+(-1)) $ maybe 0 id $ maybeHead (Map.keys store)

type InterpreterMonad = ExceptT String (ReaderT Env (StateT Store IO)) Value

fromIdent :: Ident -> String
fromIdent (Ident s) = s

initEnv :: Env
initEnv = Map.insert (Ident "println") 1 $ Map.insert (Ident "print") 0 Map.empty

initStore :: Store
initStore = Map.insert 1 printlnFun $ Map.insert 0 printFun Map.empty
  where
    printFun :: Value
    printFun = VFun (TVoid Nothing) [CopyArg Nothing (TInt Nothing) (Ident "x")] printBlock Map.empty

    printBlock :: Block
    printBlock = SBlock Nothing [SPrint Nothing (EVar Nothing (Ident "x"))]

    printlnFun :: Value
    printlnFun = VFun (TVoid Nothing) [CopyArg Nothing (TInt Nothing) (Ident "x")] printlnBlock Map.empty

    printlnBlock :: Block
    printlnBlock = SBlock Nothing [SPrintln Nothing (EVar Nothing (Ident "x"))]

execProgram :: Program -> IO ()
execProgram p = do
  (val, store) <- runStateT (runReaderT (runExceptT (evalProg p)) initEnv) initStore
  putStr $ case val of
    Right (VInt n) -> "Program finished with exit code " ++ show n ++ "\n"
    Left error -> "Runtime exception: " ++ error ++ "\n"
    Right v -> "Error: incorrect return value " ++ show v ++ "\n"
  case val of
    Right (VInt n) -> exitWith $ if n == 0 then ExitSuccess else ExitFailure $ fromIntegral n
    _ -> exitFailure


evalProg :: Program -> InterpreterMonad
evalProg (PProgram pos inits) = do
  evalStmts $ [SInit pos init | init <- inits] ++ [SRet pos $ EApp pos (Ident "main") []]

evalBlock :: Block -> InterpreterMonad
evalBlock (SBlock pos stmts) = evalStmts stmts


getDefaultForType :: Type -> Value
getDefaultForType (TInt _) = VInt 0
getDefaultForType (TStr _) = VString ""
getDefaultForType (TBool _) = VBool False
getDefaultForType (TFun _ targs t) = VFun t args block Map.empty
  where
    block :: Block
    block = SBlock Nothing [SRet Nothing $ EVal Nothing $ getDefaultForType t]

    args :: [Arg]
    args = zipWith (\ targ n -> case targ of
                  TCopyArg p t' -> CopyArg p t' (Ident $ show n)
                  TRefArg p t' -> RefArg p t' (Ident $ show n)
              ) targs [1..]
getDefaultForType (TVoid _) = VVoid

evalStmts :: [Stmt] -> InterpreterMonad

evalStmts (SEmpty pos : stmts) = evalStmts stmts

evalStmts (SBStmt pos block : stmts) = do
  evalBlock block
  evalStmts stmts

evalStmts (SDecl pos t id : stmts) = do
  store <- get
  let loc = newloc store
  modify $ Map.insert loc (getDefaultForType t)
  local (Map.insert id loc) (evalStmts stmts)

evalStmts (SInit pos (IVarDef pos' t id e) : stmts) = do
  n <- evalExpr e
  store <- get
  let loc = newloc store
  modify $ Map.insert loc n
  local (Map.insert id loc) (evalStmts stmts)

evalStmts (SInit pos def@(IFnDef pos' t id args block) : stmts) = do
  env <- ask
  store <- get
  let loc = newloc store
  let env' = Map.insert id loc env
      f = VFun t args block env'
  modify $ Map.insert loc f
  local (Map.insert id loc) (evalStmts stmts)

evalStmts (SAss pos id e : stmts) = do
  n <- evalExpr e
  env <- ask
  let Just loc = Map.lookup id env
  modify $ Map.insert loc n
  evalStmts stmts

evalStmts (SIncr pos id : stmts) = do
  env <- ask
  let Just loc = Map.lookup id env
  store <- get
  let Just (VInt n) = Map.lookup loc store
  modify $ Map.insert loc (VInt $ n + 1)
  evalStmts stmts

evalStmts (SDecr pos id : stmts) = do
  env <- ask
  let Just loc = Map.lookup id env
  store <- get
  let Just (VInt n) = Map.lookup loc store
  modify $ Map.insert loc (VInt $ n - 1)
  evalStmts stmts

evalStmts (SRet pos e : stmts) = evalExpr e

evalStmts (SVRet pos : stmts) = pure VVoid

evalStmts (SCond pos e block : stmts) = do
  b <- evalExpr e
  case b of
    VBool True -> do
      res <- evalBlock block
      case res of
        VNothing -> evalStmts stmts
        _ -> pure res
    VBool False -> do
      evalStmts stmts

evalStmts (SCondElse pos e block block': stmts) = do
  b <- evalExpr e
  case b of
    VBool True -> do
      res <- evalBlock block
      case res of
        VNothing -> evalStmts stmts
        _ -> pure res
    VBool False -> do
      res <- evalBlock block'
      case res of
        VNothing -> evalStmts stmts
        _ -> pure res

evalStmts swhile@(SWhile pos e block : stmts) = do
  b <- evalExpr e
  case b of
    VBool True -> do
      res <- evalBlock block
      case res of
        VNothing -> evalStmts swhile
        _ -> pure res
    VBool False -> do
      evalStmts stmts

evalStmts (SExp pos e : stmts) = do
  evalExpr e
  evalStmts stmts

evalStmts (SPrint pos e : stmts) = do
  v <- evalExpr e
  liftIO $ putStr $ case v of
     VInt n -> show n
     VBool b -> map Data.Char.toLower $ show b
     VString s -> s
  evalStmts stmts

evalStmts (SPrintln pos e : stmts) = do
  v <- evalExpr e
  liftIO $ putStr $ case v of
     VInt n -> show n ++ "\n"
     VBool b -> map Data.Char.toLower $ show b ++ "\n"
     VString s -> s ++ "\n"
  evalStmts stmts

evalStmts [] = pure VNothing

evalExpr :: Expr -> InterpreterMonad
evalExpr (EVar pos id) = do
  env <- ask
  let Just loc = Map.lookup id env
  store <- get
  let Just v = Map.lookup loc store
  pure v

evalExpr (EApp pos id es) = do
  env <- ask
  ns <- mapM evalExpr es
  let Just loc = Map.lookup id env
  store <- get
  let Just (VFun t args f env') = Map.lookup loc store
  let (store', env'') = foldr (
        \((e, n), arg) (store'', env''') -> case arg of
          CopyArg _ t' arg_id ->
            let loc' = newloc store'' in
            (Map.insert loc' n store'', Map.insert arg_id loc' env''')
          RefArg _ t' arg_id ->
            let EVar _ var_id = e in
            let maybeLoc' = Map.lookup var_id env in
            case maybeLoc' of
              Just loc' -> (store'', Map.insert arg_id loc' env''')
        ) (store, env') (zip (zip es ns) args)
  modify $ const store'
  v <- local (const env'') (evalBlock f)
  case v of
    VNothing -> pure $ getDefaultForType t
    _ -> pure v

evalExpr (EAppLambda pos lambda es) = do
  f <- evalExpr lambda
  store <- get
  let loc = newloc store
  modify $ Map.insert loc f
  local (Map.insert (Ident "λ") loc) $ evalExpr (EApp pos (Ident "λ") es)


evalExpr (ELitInt pos n) = pure $ VInt n

evalExpr (ELitTrue pos) = pure $ VBool True

evalExpr (ELitFalse pos) = pure $ VBool False

evalExpr (EString pos s) = pure $ VString s

evalExpr (ENeg pos e) = do
  v <- evalExpr e
  let (VInt n) = v
  pure $ VInt (-n)

evalExpr (ENot pos e) = do
  b <- evalExpr e
  case b of
    VBool True -> pure $ VBool False
    VBool False -> pure $ VBool True

evalExpr (EMul pos e op e') = do
  v <- evalExpr e
  v' <- evalExpr e'
  let (VInt n) = v
  let (VInt n') = v'
  case op of
    OTimes pos' -> pure $ VInt $ n * n'
    ODiv pos' -> if n' /= 0 then pure $ VInt $ n `div` n' else throwError $ "Division by zero at " ++ showPos pos
    OMod pos' -> if n' /= 0 then pure $ VInt $ n `mod` n' else throwError $ "Division by zero at " ++ showPos pos


evalExpr (EAdd pos e op e') = do
  v <- evalExpr e
  v' <- evalExpr e'
  let (VInt n) = v
  let (VInt n') = v'
  case op of
    OPlus pos' -> pure $ VInt $ n + n'
    OMinus pos' -> pure $ VInt $ n - n'

evalExpr (ERel pos e op e') = do
  v <- evalExpr e
  v' <- evalExpr e'
  pure $ VBool $ case (v, v') of
    (VInt n, VInt n') ->
      case op of
        OLTH pos' -> n < n'
        OLE pos' -> n <= n'
        OGTH pos' -> n > n'
        OGE pos' -> n >= n'
        OEQU pos' -> n == n'
        ONE pos' -> n /= n'
    (VBool b, VBool b') ->
      case op of
        OEQU pos' -> b == b'
        ONE pos' -> b /= b'
    (VString s, VString s') ->
      case op of
        OEQU pos' -> s == s'
        ONE pos' -> s /= s'

evalExpr (EAnd pos e e') = do
  v <- evalExpr e
  v' <- evalExpr e'
  let (VBool b) = v
  let (VBool b') = v'
  pure $ VBool $ b && b'

evalExpr (EOr pos e e') = do
  v <- evalExpr e
  v' <- evalExpr e'
  let (VBool b) = v
  let (VBool b') = v'
  pure $ VBool $ b || b'

evalExpr (ELambdaBlock pos args t block) = do
  env <- ask
  let f = VFun t args block env
  pure f

evalExpr (ELambdaExpr pos args t e) = do
  env <- ask
  store <- get
  let loc = newloc store
      block = SBlock pos [SRet pos e]
      f = VFun t args block env
  pure f

evalExpr (EVal pos value) = pure value