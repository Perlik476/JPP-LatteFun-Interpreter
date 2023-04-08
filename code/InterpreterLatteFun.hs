-- File generated by the BNF Converter (bnfc 2.9.4.1).

-- | Program to test parser.
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Main where

import Prelude
import System.Environment ( getArgs )
import System.Exit        ( exitFailure )
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
      putStrV v "Tokens:"
      mapM_ (putStrV v . showPosToken . mkPosToken) ts
      putStrLn err
      exitFailure
    Right tree -> do
      -- putStrLn "\nParse Successful!"
      execProgram tree
      -- showTree v tree
  where
  ts = myLexer s
  showPosToken ((l,c),t) = concat [ show l, ":", show c, "\t", show t ]

maybeHead :: [a] -> Maybe a
maybeHead (x:_) = Just x
maybeHead _ = Nothing

newloc :: Store -> Loc
newloc store = (+(-1)) $ maybe 0 id $ maybeHead (Map.keys store)

type IM a = ExceptT String (ReaderT Env (StateT Store IO)) a

showPos :: BNFC'Position -> String
showPos (Just (line, col)) = "line " ++ show line ++ ", column " ++ show col
showPos Nothing = "unknown location"

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
  putStr $ "Store size at exit: " ++ show (length store) ++ "\n"
  pure ()

evalProg :: Program -> IM Value
evalProg (PProgram pos inits) = do
  evalStmts $ [SInit pos init | init <- inits] ++ [SExp pos $ EApp pos (Ident "main") []]

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
  let maybeLoc = Map.lookup id env
  case maybeLoc of
    Nothing -> throwError $ "Variable " ++ fromIdent id ++ " not in scope"
    Just loc -> do
      modify $ Map.insert loc n
      evalStmts stmts

evalStmts (SIncr pos id : stmts) = do
  env <- ask
  let maybeLoc = Map.lookup id env
  case maybeLoc of
    Nothing -> throwError $ "Variable " ++ fromIdent id ++ " not in scope"
    Just loc -> do
      store <- get
      let maybeValue = Map.lookup loc store
      case maybeValue of
        Nothing -> throwError "impossible"
        Just (VInt n) -> do
          modify $ Map.insert loc (VInt $ n + 1)
          evalStmts stmts

evalStmts (SDecr pos id : stmts) = do
  env <- ask
  let maybeLoc = Map.lookup id env
  case maybeLoc of
    Nothing -> throwError $ "Variable " ++ fromIdent id ++ " not in scope"
    Just loc -> do
      store <- get
      let maybeValue = Map.lookup loc store
      case maybeValue of
        Nothing -> throwError "impossible"
        Just (VInt n) -> do
          modify $ Map.insert loc (VInt $ n - 1)
          evalStmts stmts

evalStmts (SRet pos e : stmts) = do
  n <- evalExpr e
  pure n

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

evalStmts (SExp pos e : []) = evalExpr e

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
  let maybeLoc = Map.lookup id env
  case maybeLoc of
    Nothing -> throwError $ "Variable " ++ fromIdent id ++ " is not defined (env) at " ++ showPos pos
    Just loc -> do
      store <- get
      let maybeVar = Map.lookup loc store
      case maybeVar of
        Nothing -> throwError $ "Variable " ++ fromIdent id ++ " is not defined (store) at " ++ showPos pos
        Just v -> pure v

evalExpr (EApp pos id es) = do
  env <- ask
  ns <- mapM evalExpr es -- TODO - to raczej nie powinno się zawsze obliczać? to może generować potencjalne niechciane efekty uboczne
  let maybeLoc = Map.lookup id env
  case maybeLoc of
    Nothing -> throwError $ "Function " ++ fromIdent id ++ " is not defined (at " ++ showPos pos ++ ")"
    Just loc -> do
      store <- get
      let maybeFun = Map.lookup loc store
      case maybeFun of
        Nothing -> throwError $ "Function " ++ fromIdent id ++ " is not defined (at " ++ showPos pos ++ ")"
        Just (VFun t args f env') -> do
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
          local (const env'') (evalBlock f)
        Just value -> throwError $ "Internal error: expected function in store at " ++ showPos pos ++ ", got " ++ show value

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
  let (VInt n) = v
  let (VInt n') = v'
  pure $ VBool $ case op of
    OLTH pos' -> n < n'
    OLE pos' -> n <= n'
    OGTH pos' -> n > n'
    OGE pos' -> n >= n'
    OEQU pos' -> n == n'
    ONE pos' -> n /= n'

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