-- File generated by the BNF Converter (bnfc 2.9.4.1).

-- | Program to test parser.
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Main where

import Prelude
import System.Environment ( getArgs )
import System.Exit
import Control.Monad      ( when )

import AbsLatteFun
import LexLatteFun
import ParLatteFun
import PrintLatteFun
import SkelLatteFun  ()
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as Map
import Data.Maybe

type Err        = Either String
type ParseFun a = [Token] -> Err a
type Verbosity  = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ putStrLn s

-- runFile :: (Print a, Show a) => Verbosity -> ParseFun a -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run v p

-- run :: (Print a, Show a) => Verbosity -> ParseFun a -> String -> IO ()
run v p s =
  case p ts of
    Left err -> do
      putStrLn "\nParse              Failed...\n"
      putStrLn err
      exitFailure
    Right tree -> do
      success <- typeCheck tree
      if success then
        execProgram tree
      else
        exitFailure
  where
  ts = myLexer s
  showPosToken ((l,c),t) = concat [ show l, ":", show c, "\t", show t ]

maybeHead :: [a] -> Maybe a
maybeHead (x:_) = Just x
maybeHead _ = Nothing

newloc :: Store -> Loc
newloc store = (+(-1)) $ maybe 0 id $ maybeHead (Map.keys store)

type IM a = ExceptT String (ReaderT Env (StateT Store IO)) a
type TM a = ExceptT String (ReaderT TEnv IO) a

showPos :: BNFC'Position -> String
showPos (Just (line, col)) = "line " ++ show line ++ ", column " ++ show col
showPos Nothing = "unknown location"

fromIdent :: Ident -> String
fromIdent (Ident s) = s

initEnv :: Env
initEnv = Map.insert (Ident "println") 1 $ Map.insert (Ident "print") 0 Map.empty

initTEnv :: TEnv
initTEnv = Map.insert (Ident "println") TPrint $ Map.insert (Ident "print") TPrint Map.empty

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
  putStr $ "Store size at exit: " ++ show (length store) ++ "\n"
  case val of
    Right (VInt n) -> exitWith $ if n == 0 then ExitSuccess else ExitFailure $ fromIntegral n
    _ -> exitFailure


evalProg :: Program -> IM Value
evalProg (PProgram pos inits) = do
  evalStmts $ [SInit pos init | init <- inits] ++ [SRet pos $ EApp pos (Ident "main") []]

evalBlock :: Block -> IM Value
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

evalStmts :: [Stmt] -> IM Value

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

evalStmts (SInit pos (IFnDef pos' t id args block) : stmts) = do
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
     VBool b -> show b
     VString s -> s
  evalStmts stmts

evalStmts (SPrintln pos e : stmts) = do
  v <- evalExpr e
  liftIO $ putStr $ case v of
     VInt n -> show n ++ "\n"
     VBool b -> show b ++ "\n"
     VString s -> s ++ "\n"
  evalStmts stmts

evalStmts [] = pure VNothing

evalExpr :: Expr -> IM Value
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
  let Just value = Map.lookup loc store
  case value of
    (VFun t args f env') -> do
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
    _ -> throwError $ "Internal error: expected function in store at " ++ showPos pos ++ ", got " ++ show value

evalExpr (EAppLambda pos lambda es) = do
  f <- evalExpr lambda
  store <- get
  let loc = newloc store -- TODO nie trzeba przecież tego robić
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
    OMod pos' -> pure $ VInt $ n `mod` n'

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



typeCheck :: Program -> IO Bool
typeCheck p = do
  result <- runReaderT (runExceptT (typeCheckProg p)) initTEnv
  case result of
    Left error -> do
      putStr $ error ++ "\n"
      pure False
    Right _ -> pure True

typeCheckProg :: Program -> TM Type
typeCheckProg (PProgram pos inits) = do
  typeCheckStmts [SInit pos init | init <- inits]

typeCheckBlock :: Block -> TM Type
typeCheckBlock (SBlock pos stmts) = typeCheckStmts stmts


showType :: Type -> String
showType (TBool pos) = "bool (at " ++ showPos pos ++ ")"
showType (TInt pos) = "int (at " ++ showPos pos ++ ")"
showType (TStr pos) = "string (at " ++ showPos pos ++ ")"
showType (TVoid pos) = "void (at " ++ showPos pos ++ ")"
showType (TAuto pos) = "auto (at " ++ showPos pos ++ ")"
showType (TFun pos args t) = "[(" ++ showArgs args ++ ") -> " ++ showType' t ++ "] (at " ++ showPos pos ++ ")"
showType TPrint = "[(int | bool | string) -> void] (print)"

showType' :: Type -> String
showType' (TBool _) = "bool"
showType' (TInt _) = "int"
showType' (TStr _) = "string"
showType' (TVoid _) = "void"
showType' (TAuto _) = "auto"
showType' (TFun _ args t) = "[(" ++ showArgs args ++ ") -> " ++ showType' t ++ "]"

showArgs :: [TArg] -> String
showArgs [arg] = showArg arg
showArgs [] = ""
showArgs (arg:args) = showArg arg ++ ", " ++ showArgs args

showArg :: TArg -> String
showArg (TCopyArg _ t) = showType' t
showArg (TRefArg _ t) = "ref " ++ showType' t


sameType :: Type -> Type -> Bool
sameType (TInt _) (TInt _) = True
sameType (TStr _) (TStr _) = True
sameType (TBool _) (TBool _) = True
sameType (TVoid _) (TVoid _) = True
sameType (TFun _ t_args t_ret) (TFun _ t_args' t_ret') = sameType t_ret t_ret'
  && length t_args == length t_args'
  && foldr (\(t, t') res -> res && sameTypeArg t t') True (zip t_args t_args')
sameType (TAuto _) _ = True
sameType _ (TAuto _) = True
sameType TPrint TPrint = True
sameType _ _ = False

sameTypeArg :: TArg -> TArg -> Bool
sameTypeArg (TCopyArg _ t) (TCopyArg _ t') = sameType t t'
sameTypeArg (TRefArg _ t) (TRefArg _ t') = sameType t t'
sameTypeArg _ _ = False

isTVoid :: Type -> Bool
isTVoid (TVoid _) = True
isTVoid _ = False

isTFunWithTAuto :: Type -> Bool
isTFunWithTAuto (TFun _ t_args t_ret) =
  isTAuto t_ret || foldr ((\t res -> res || isTAuto t) . targToType) False t_args
isTFunWithTAuto _ = False

isTAuto :: Type -> Bool
isTAuto (TAuto _) = True
isTAuto _ = False

argToTArg :: Arg -> TArg
argToTArg (CopyArg pos t _) = TCopyArg pos t
argToTArg (RefArg pos t _) = TRefArg pos t

argToId :: Arg -> Ident
argToId (CopyArg _ _ id) = id
argToId (RefArg _ _ id) = id

targToType :: TArg -> Type
targToType (TCopyArg _ t) = t
targToType (TRefArg _ t) = t


typeCheckStmts :: [Stmt] -> TM Type
typeCheckStmts (SEmpty pos : stmts) = pure $ TVoid pos

typeCheckStmts (SBStmt pos block : stmts) = do
  typeCheckBlock block
  typeCheckStmts stmts

typeCheckStmts (SDecl pos t id : stmts) = do
  case t of
    TAuto _ -> throwError $ "Auto used without initialization at " ++ showPos pos
    _ -> local (Map.insert id t) (typeCheckStmts stmts)

typeCheckStmts (SInit pos (IVarDef pos' t id e) : stmts) = do
  if isTVoid t then
    throwError $ "Variable " ++ fromIdent id ++ " has type void at " ++ showPos pos
  else if isTFunWithTAuto t then
    throwError $ "Variable " ++ fromIdent id ++ " has functional type with auto argument or return value at " ++ showPos pos
  else do
    t_e <- typeCheckExpr e
    if isTVoid t_e then
      throwError $ "Cannot assign void expression to variable " ++ fromIdent id ++ " at " ++ showPos pos
    else if sameType t t_e || isTAuto t then
      local (Map.insert id t_e) (typeCheckStmts stmts)
    else
      throwError $ "Type mismatch: " ++ showType t ++ " and " ++ showType t_e

typeCheckStmts (SInit pos (IFnDef pos' t id args block) : stmts) = do -- TODO
  env <- ask
  let t_args = map (targToType . argToTArg) args
      proper = foldr (\t' res -> res && not (isTAuto t') && not (isTVoid t') && not (isTFunWithTAuto t')) True t_args
      id_args = map argToId args
  if not proper then
    throwError $ "Argument type is void or contains auto at " ++ showPos pos
  else do
    let env' = foldr (\(id', t') env'' -> Map.insert id' t' env'') env $ (id, t_fun):zip id_args t_args
        t_fun = TFun pos' (map argToTArg args) t
    t' <- local (const env') (typeCheckBlock block)
    if (sameType t t' && not (isTAuto t')) || (isTAuto t' && not (isTAuto t)) then do
      let t_real = if not (isTAuto t) then t else t'
          t_fun' = TFun pos' (map argToTArg args) t_real
          env'' = Map.insert id t_fun' env'
      local (const env'') (typeCheckStmts stmts)
    else
      throwError $ "Type mismatch: " ++ showType t ++ " and " ++ showType t'

typeCheckStmts (SAss pos id e : stmts) = do
  t_e <- typeCheckExpr e
  if isTVoid t_e then
    throwError $ "Cannot assign void expression to variable " ++ fromIdent id ++ " at " ++ showPos pos
  else do
    env <- ask
    let maybeType = Map.lookup id env
    case maybeType of
      Nothing -> throwError $ "Variable " ++ fromIdent id ++ " not in scope at " ++ showPos pos
      Just t -> do
        if not $ sameType t t_e then
          throwError $ "Type mismatch: " ++ showType t ++ " and " ++ showType t_e
        else
          typeCheckStmts stmts

typeCheckStmts (SIncr pos id : stmts) = do
  env <- ask
  let maybeType = Map.lookup id env
  case maybeType of
    Nothing -> throwError $ "Variable " ++ fromIdent id ++ " not in scope at " ++ showPos pos
    Just t -> do
      let t_e = TInt pos
      if not $ sameType t t_e then
        throwError $ "Type mismatch: " ++ showType t ++ " is not of type int at " ++ showPos pos
      else
        typeCheckStmts stmts

typeCheckStmts (SDecr pos id : stmts) = typeCheckStmts (SIncr pos id : stmts)

typeCheckStmts (SRet pos e : stmts) = typeCheckExpr e

typeCheckStmts (SVRet pos : stmts) = pure $ TVoid pos

typeCheckStmts (SCond pos e block : stmts) = do
  t <- typeCheckExpr e
  case t of
    TBool _ -> do
      t1 <- typeCheckBlock block
      t2 <- typeCheckStmts stmts
      if sameType t1 t2 then
        pure t2
      else
        throwError $ "Type mismatch: Different return values in function definition at " ++ showPos pos ++ ": " ++ showType t1 ++ " and " ++ showType t2
    _ -> do
      throwError $ "Type mismatch: " ++ showType t ++ " is not of type bool at " ++ showPos pos

typeCheckStmts (SCondElse pos e block block': stmts) = do
  t <- typeCheckExpr e
  case t of
    TBool _ -> do
      t1 <- typeCheckBlock block
      t2 <- typeCheckBlock block'
      t3 <- typeCheckStmts stmts
      if sameType t1 t2 && sameType t2 t3 then
        if not (isTAuto t1) && not (isTAuto t2) then pure t1
        else if not (isTAuto t3) then pure t3
        else throwError $ "Type mismatch: Different return values in function definition at " ++ showPos pos
      else
        throwError $ "Type mismatch: Different return values in function definition at " ++ showPos pos
    _ -> do
      throwError $ "Type mismatch: " ++ showType t ++ " is not of type bool at " ++ showPos pos

typeCheckStmts (SWhile pos e block : stmts) = do
  t <- typeCheckExpr e
  case t of
    TBool _ -> do
      t1 <- typeCheckBlock block
      t2 <- typeCheckStmts stmts
      if sameType t1 t2 then
        pure t2
      else
        throwError $ "Type mismatch: Different return values in function definition at " ++ showPos pos
    _ -> do
      throwError $ "Type mismatch: " ++ showType t ++ " is not of type bool at " ++ showPos pos

typeCheckStmts (SExp pos e : []) = do
  typeCheckExpr e
  pure (TAuto pos)

typeCheckStmts (SExp pos e : stmts) = do
  typeCheckExpr e
  typeCheckStmts stmts

typeCheckStmts (SPrint pos e : stmts) = do
  t <- typeCheckExpr e
  case t of
    TInt _ -> typeCheckStmts stmts
    TBool _ -> typeCheckStmts stmts
    TStr _ -> typeCheckStmts stmts
    _ -> throwError $ "Type mismatch: " ++ showType t ++ " is not of basic type (bool/int/string) at " ++ showPos pos


typeCheckStmts (SPrintln pos e : stmts) = typeCheckStmts (SPrint pos e : stmts)

typeCheckStmts [] = pure $ TAuto Nothing -- TODO?



typeCheckExpr :: Expr -> TM Type
typeCheckExpr (EVar pos id) = do
  env <- ask
  let maybeType = Map.lookup id env
  case maybeType of
    Nothing -> throwError $ "Variable " ++ fromIdent id ++ " is not defined at " ++ showPos pos
    Just t -> pure t

typeCheckExpr (EApp pos id es) = do
  env <- ask
  ts <- mapM typeCheckExpr es
  let maybeType = Map.lookup id env
  case maybeType of
    Nothing -> throwError $ "Function " ++ fromIdent id ++ " is not defined at " ++ showPos pos
    Just t@(TFun pos' t_args t') -> do
      if length t_args == length ts then
        if foldr (\(t1, t2) res -> sameType t1 t2 && res) True (zip (map targToType t_args) ts) then
            if foldr (
              \(t_arg, e) res -> case t_arg of
                TRefArg _ _ -> case e of
                  EVar _ _ -> res
                  _ -> False
                _ -> res
            ) True (zip t_args es) then
              pure t'
            else
              throwError $ "Type mismatch: expected a ref argument at " ++ showPos pos
          else
            throwError $ "Type mismatch: one of arguments is of incorrect type at " ++ showPos pos
        else
          throwError ("Inorrect number of arguments to function " ++ fromIdent id ++ " of type " ++ showType t ++ " at " ++ showPos pos ++ ".\n"
            ++ "Expected " ++ show (length t_args) ++ ", got " ++ show (length ts))
    Just TPrint -> do
      if length ts == 1 then do
        let t' = head ts
        case t' of
          TInt _ -> pure $ TVoid pos
          TBool _ -> pure $ TVoid pos
          TStr _ -> pure $ TVoid pos
          _ -> throwError $ "Type mismatch: " ++ showType t' ++ " is not of basic type (bool/int/string) at " ++ showPos pos
      else
        throwError $ "Type mismatch: print requires exactly one argument at " ++ showPos pos
    Just t -> throwError $ "Type mismatch: expected a function at " ++ showPos pos ++ ", got " ++ showType t

typeCheckExpr (EAppLambda pos lambda es) = do
  t <- typeCheckExpr lambda
  local (Map.insert (Ident "λ") t) $ typeCheckExpr (EApp pos (Ident "λ") es)


typeCheckExpr (ELitInt pos _) = pure $ TInt pos

typeCheckExpr (ELitTrue pos) = pure $ TBool pos

typeCheckExpr (ELitFalse pos) = pure $ TBool pos

typeCheckExpr (EString pos _) = pure $ TStr pos

typeCheckExpr (ENeg pos e) = do
  t <- typeCheckExpr e
  case t of
    TInt pos -> pure t
    _ -> throwError $ "Type mismatch: Expected int at " ++ showPos pos ++ ", got " ++ showType t

typeCheckExpr (ENot pos e) = do
  t <- typeCheckExpr e
  case t of
    TBool pos -> pure t
    _ -> throwError $ "Type mismatch: Expected bool at " ++ showPos pos ++ ", got " ++ showType t

typeCheckExpr (EMul pos e op e') = do
  t <- typeCheckExpr e
  t' <- typeCheckExpr e'
  case (t, t') of
    (TInt _, TInt _) -> pure $ TInt pos
    _ -> throwError $ "Type mismatch: Expected two ints at " ++ showPos pos ++ ", got " ++ showType t ++ " and " ++ showType t'

typeCheckExpr (EAdd pos e op e') = typeCheckExpr (EMul pos e (OTimes pos) e')

typeCheckExpr (ERel pos e op e') = do
  t <- typeCheckExpr e
  t' <- typeCheckExpr e'
  case (t, t') of
    (TInt _, TInt _) -> pure $ TBool pos
    (TBool _, TBool _) ->
      case op of
        OEQU pos' -> pure $ TBool pos
        ONE pos' -> pure $ TBool pos
        _ -> throwError $ "Type mismatch: Expected two ints at " ++ showPos pos ++ ", got " ++ showType t ++ " and " ++ showType t'
    (TStr _, TStr _) ->
      case op of
        OEQU pos' -> pure $ TBool pos
        ONE pos' -> pure $ TBool pos
        _ -> throwError $ "Type mismatch: Expected two ints at " ++ showPos pos ++ ", got " ++ showType t ++ " and " ++ showType t'
    _ -> throwError $ "Type mismatch: Expected two basic type expressions (int/bool/string) at " ++ showPos pos ++ ", got " ++ showType t ++ " and " ++ showType t'

typeCheckExpr (EAnd pos e e') = do
  t <- typeCheckExpr e
  t' <- typeCheckExpr e'
  case (t, t') of
    (TBool _, TBool _) -> pure $ TBool pos
    _ -> throwError $ "Type mismatch: Expected two bools at " ++ showPos pos ++ ", got " ++ showType t ++ " and " ++ showType t'

typeCheckExpr (EOr pos e e') = typeCheckExpr (EAnd pos e e')

typeCheckExpr (ELambdaBlock pos args t block) = do
  env <- ask
  let t_args = map (targToType . argToTArg) args
      proper = foldr (\t' res -> res && not (isTAuto t') && not (isTVoid t') && not (isTFunWithTAuto t')) True t_args
      id_args = map argToId args
  if not proper then
    throwError $ "Argument type is void or contains auto at " ++ showPos pos
  else do
    let env' = foldr (\(id', t') env'' -> Map.insert id' t' env'') env $ zip id_args t_args
        t_fun = TFun pos (map argToTArg args) t
    t' <- local (const env') (typeCheckBlock block)
    if (sameType t t' && not (isTAuto t')) || (isTAuto t' && not (isTAuto t)) then do
      let t_real = if not (isTAuto t) then t else t'
          t_fun' = TFun pos (map argToTArg args) t_real
      pure t_fun'
    else
      throwError $ "Type mismatch: " ++ showType t ++ " and " ++ showType t'

typeCheckExpr (ELambdaExpr pos args t e) = do
  env <- ask
  let t_args = map (targToType . argToTArg) args
      proper = foldr (\t' res -> res && not (isTAuto t') && not (isTVoid t') && not (isTFunWithTAuto t')) True t_args
      id_args = map argToId args
  if not proper then
    throwError $ "Argument type is void or contains auto at " ++ showPos pos
  else do
    let env' = foldr (\(id', t') env'' -> Map.insert id' t' env'') env $ zip id_args t_args
        t_fun = TFun pos (map argToTArg args) t
    t' <- local (const env') (typeCheckExpr e)
    if (sameType t t' && not (isTAuto t')) || (isTAuto t' && not (isTAuto t)) then do
      let t_real = if not (isTAuto t) then t else t'
          t_fun' = TFun pos (map argToTArg args) t_real
      pure t_fun'
    else
      throwError $ "Type mismatch: " ++ showType t ++ " and " ++ showType t'

typeCheckExpr (EVal pos VNothing) = pure $ TVoid pos


showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree = do
  putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
  putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin verbosely."
    , "  (files)         Parse content of files verbosely."
    , "  -s (files)      Silent mode. Parse content of files silently."
    ]

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    []         -> getContents >>= run 2 pProgram
    "-s":fs    -> mapM_ (runFile 0 pProgram) fs
    fs         -> mapM_ (runFile 2 pProgram) fs