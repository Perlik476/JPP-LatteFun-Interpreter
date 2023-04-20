{-# LANGUAGE FlexibleInstances #-}

module TypeChecker(typeCheck) where

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
import Data.List (intercalate)

type TypeMonad = ExceptT Error (ReaderT TEnv IO) Type

type Error = Error' BNFC'Position
data Error' a
  = TypeMismatch a Type Type
  | TypeMismatchOptions a [Type] Type
  | AssignmentFailure a Var Type Type
  | DeclarationFailure a Var Type
  | NotInScope a Var
  | TypeDeductionFailure a
  | ReturnTypeMismatch a [Type]
  | FunctionWrongNumberOfArguments a Var Type Int Int
  | FunctionWrongArgumentType a Var Type Int Type Type
  | FunctionRefArgument a Var Type Int
  | NotAFunction a Var Type
  | MainError a String

instance Show Error where
  show err =
    case err of
      TypeMismatch pos t t' ->
        concat ["Type mismatch at ", showPos pos, ".\n", "Expected ", showType t, ", got ", showType t', "."]
      TypeMismatchOptions pos ts t' ->
        concat ["Type mismatch at ", showPos pos, ".\n", "Expected one of the following types: ", showTypes ts, ", got ", showType t', "."]
      AssignmentFailure pos id t t' ->
        concat ["Assignment failure (type mismatch) at ", showPos pos, ".\n", "Cannot assign value of type ", showType t', " to variable ",
          fromIdent id, " of type ", showType t, "."]
      DeclarationFailure pos id t ->
        concat ["Declaration failure at ", showPos pos, ".\n", "Variable ", fromIdent id, " cannot be declared with type ", showType t, "."]
      NotInScope pos id ->
        concat ["Unknown identifier at ", showPos pos, ".\n", "Variable ", fromIdent id, " not in scope."]
      TypeDeductionFailure pos ->
        concat ["Type deduction failure at ", showPos pos, ".\n", "Inferring of auto type failed in function definition."]
      ReturnTypeMismatch pos ts ->
        concat ["Type deduction failure at ", showPos pos, ".\n", "Encountered values of different types returned in function definition: ",
          showTypes ts, "."]
      FunctionWrongNumberOfArguments pos id t_fun n n' ->
        concat ["Function application failure at ", showPos pos, " in function ", fromIdent id, " of type ", showType t_fun, ".\n",
          "Incorrect number of arguments. Expected ", show n, ", got ", show n', "."]
      FunctionWrongArgumentType pos id t_fun n t t' ->
        concat ["Function application failure (type mismatch) at ", showPos pos, " in function ", fromIdent id, " of type ", showType t_fun,
          ".\n", "Expected ", showType t, " as argument number ", show n, ", got ", showType t', "."]
      FunctionRefArgument pos id t_fun n ->
        concat ["Function application failure at (reference type) at ", showPos pos, " in function ", fromIdent id, " of type ", showType t_fun,
          ".\n", "Expected a variable as argument number ", show n, ", got an expression."]
      NotAFunction pos id t ->
        concat ["Function application failure (type mismatch) at ", showPos pos, ".\n", "Variable ", fromIdent id, " of type ", showType t,
          " is not a function."]
      MainError pos message -> 
        concat ["Function main error at ", showPos pos, ".\n", message]


fromIdent :: Ident -> String
fromIdent (Ident s) = s

initTEnv :: TEnv
initTEnv = Map.insert (Ident "println") (TPrint Nothing) $ Map.insert (Ident "print") (TPrint Nothing) Map.empty


typeCheck :: Program -> IO Bool
typeCheck p = do
  result <- runReaderT (runExceptT (typeCheckProg p)) initTEnv
  case result of
    Left error -> do
      putStr "Static type checking failed.\n"
      putStr $ show error ++ "\n"
      pure False
    Right _ -> pure True

typeCheckProg :: Program -> TypeMonad
typeCheckProg (PProgram pos inits) = do
  initsContainMain inits
  typeCheckStmts [SInit (getInitPos init) init | init <- inits]

initsContainMain :: [Init] -> TypeMonad
initsContainMain ((IVarDef pos _ id _) : inits) =
  if fromIdent id /= "main" then initsContainMain inits
  else throwError $ MainError pos "Illegal toplevel variable name main."
initsContainMain ((IFnDef pos t id args block) : inits) = do
  if fromIdent id /= "main" then initsContainMain inits
  else
    if not $ sameType t (TInt Nothing) then
      throwError $ MainError pos "Function main should have int as return type."
    else if not (null args) then
      throwError $ MainError pos "Function main should have no arguments."
    else
      if any (\ini -> fromIdent (getInitId ini) == "main") inits then
        throwError $ MainError Nothing "Multiple definitions of main in the toplevel."
      else
        pure t
initsContainMain [] = throwError $ MainError Nothing "Function main is not defined."


getInitPos :: Init -> BNFC'Position
getInitPos (IVarDef pos _ _ _) = pos
getInitPos (IFnDef pos _ _ _ _) = pos

getInitId :: Init -> Ident
getInitId (IVarDef _ _ id _) = id
getInitId (IFnDef _ _ id _ _) = id

typeCheckBlock :: Block -> TypeMonad
typeCheckBlock (SBlock pos stmts) = typeCheckStmts stmts


showType :: Type -> String
showType t = showType' t ++ showPos' (hasPosition t)

showPos' :: BNFC'Position -> String
showPos' pos = case pos of
  Just _ -> " (at " ++ showPos pos ++ ")"
  Nothing -> ""

showType' :: Type -> String
showType' (TBool _) = "bool"
showType' (TInt _) = "int"
showType' (TStr _) = "string"
showType' (TVoid _) = "void"
showType' (TAuto _) = "auto"
showType' (TFun _ args t) = "[(" ++ showArgs args ++ ") -> " ++ showType' t ++ "]"
showType' (TPrint _) = "[(int | bool | string) -> void] (print)"

showTypes :: [Type] -> String
showTypes = intercalate ", " . map showType

showArgs :: [TArg] -> String
showArgs [arg] = showArg arg
showArgs [] = ""
showArgs (arg:args) = showArg arg ++ ", " ++ showArgs args

showArg :: TArg -> String
showArg (TCopyArg _ t) = showType' t
showArg (TRefArg _ t) = showType' t ++ " ref"


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
sameType (TPrint _) (TPrint _) = True
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
  isTAuto t_ret || foldr ((\t res -> res || isTAuto t || isTFunWithTAuto t) . fromTArgToType) False t_args
isTFunWithTAuto _ = False

isTAuto :: Type -> Bool
isTAuto (TAuto _) = True
isTAuto _ = False

containsTAuto :: Type -> Bool
containsTAuto t = isTFunWithTAuto t || isTAuto t

fromArgToTArg :: Arg -> TArg
fromArgToTArg (CopyArg pos t _) = TCopyArg pos t
fromArgToTArg (RefArg pos t _) = TRefArg pos t

fromArgToId :: Arg -> Ident
fromArgToId (CopyArg _ _ id) = id
fromArgToId (RefArg _ _ id) = id

fromTArgToType :: TArg -> Type
fromTArgToType (TCopyArg _ t) = t
fromTArgToType (TRefArg _ t) = t


checkArgumentTypes :: BNFC'Position -> Ident -> Type -> [Type] -> TypeMonad
checkArgumentTypes pos id t_fun@(TFun _ t_args _) ts = 
  checkArgumentTypes' 1 (map fromTArgToType t_args) ts
  where
    checkArgumentTypes' :: Int -> [Type] -> [Type] -> TypeMonad
    checkArgumentTypes' n (t:ts) (t':ts') =
      if sameType t t' then checkArgumentTypes' (n + 1) ts ts'
      else throwError $ FunctionWrongArgumentType pos id t_fun n t t'
    checkArgumentTypes' _ _ _ = pure $ TAuto Nothing
checkArgumentTypes pos id t _ = throwError $ NotAFunction pos id t

checkRefArguments :: BNFC'Position -> Ident -> Type -> [Expr] -> TypeMonad
checkRefArguments pos id t_fun@(TFun _ t_args _) es = 
  checkRefArguments' 1 t_args es
  where
    checkRefArguments' :: Int -> [TArg] -> [Expr] -> TypeMonad
    checkRefArguments' n (t:ts) (e:es) =
      case t of
        TRefArg _ _ ->
          case e of
            EVar _ _ -> checkRefArguments' (n + 1) ts es
            _ -> throwError $ FunctionRefArgument pos id t_fun n
        _ -> checkRefArguments' (n + 1) ts es
    checkRefArguments' _ _ _ = pure $ TAuto Nothing
checkRefArguments pos id t _ = throwError $ NotAFunction pos id t


checkVoidArguments :: [Arg] -> TypeMonad 
checkVoidArguments args = checkVoidArguments' 1 t_args
  where
    t_args = map (fromTArgToType . fromArgToTArg) args
    id_args = map fromArgToId args
    checkVoidArguments' :: Int -> [Type] -> TypeMonad
    checkVoidArguments' n (t:ts) =
      case t of
        TVoid pos -> throwError $ DeclarationFailure pos (id_args!!n) t
        _ -> checkVoidArguments' (n + 1) ts
    checkVoidArguments' _ _ = pure $ TAuto Nothing

checkAutoArguments :: [Arg] -> TypeMonad
checkAutoArguments args = checkAutoArguments' 1 t_args
  where 
    t_args = map (fromTArgToType . fromArgToTArg) args
    id_args = map fromArgToId args
    checkAutoArguments' :: Int -> [Type] -> TypeMonad
    checkAutoArguments' n (t:ts) =
      if containsTAuto t then throwError $ DeclarationFailure (hasPosition t) (id_args!!n) t
      else checkAutoArguments' (n + 1) ts
    checkAutoArguments' _ _ = pure $ TAuto Nothing


createFunctionEnv :: [Arg] -> TEnv -> TEnv
createFunctionEnv args env = 
  foldr (
    \(id', t') env'' -> Map.insert id' t' env''
  ) env $ zip id_args t_args
  where
    t_args = map (fromTArgToType . fromArgToTArg) args
    id_args = map fromArgToId args


typeCheckStmts :: [Stmt] -> TypeMonad
typeCheckStmts (SEmpty pos : stmts) = typeCheckStmts stmts

typeCheckStmts (SBStmt pos block : stmts) = do
  typeCheckBlock block
  typeCheckStmts stmts

typeCheckStmts (SDecl pos t id : stmts) = do
  case t of
    TAuto _ -> throwError $ DeclarationFailure pos id t
    TVoid _ -> throwError $ DeclarationFailure pos id t
    _ -> local (Map.insert id t) (typeCheckStmts stmts)

typeCheckStmts (SInit pos (IVarDef pos' t id e) : stmts) = do
  if isTVoid t || isTFunWithTAuto t then
    throwError $ DeclarationFailure pos id t
  else do
    t_e <- typeCheckExpr e
    if isTVoid t_e then
      throwError $ AssignmentFailure pos id t t_e
    else if sameType t t_e || isTAuto t then
      local (Map.insert id t_e) (typeCheckStmts stmts)
    else
      throwError $ AssignmentFailure pos id t t_e

typeCheckStmts (SInit pos (IFnDef pos' t id args block) : stmts) = do
  env <- ask
  checkVoidArguments args
  checkAutoArguments args
  let env' = Map.insert id t_fun $ createFunctionEnv args env
      t_fun = TFun pos' (map fromArgToTArg args) t''
      t'' = if isTFunWithTAuto t then TAuto pos else t
  t' <- local (const env') (typeCheckBlock block)

  if (sameType t t' && not (isTAuto t')) || (isTAuto t' && not (isTAuto t)) then do
    let t_real = if not (isTAuto t'') then t'' else t'
        t_fun' = TFun pos' (map fromArgToTArg args) t_real
        env'' = Map.insert id t_fun' env'
    local (const env'') (typeCheckStmts stmts)
  else if isTAuto t && isTAuto t' then
    throwError $ TypeDeductionFailure pos
  else
    throwError $ TypeMismatch pos t t'

typeCheckStmts (SAss pos id e : stmts) = do
  t_e <- typeCheckExpr e
  env <- ask
  let maybeType = Map.lookup id env
  case maybeType of
    Nothing -> throwError $ NotInScope pos id
    Just t -> do
      if not $ sameType t t_e then
        throwError $ AssignmentFailure pos id t t_e
      else
        typeCheckStmts stmts

typeCheckStmts (SIncr pos id : stmts) = do
  env <- ask
  let maybeType = Map.lookup id env
  case maybeType of
    Nothing -> throwError $ NotInScope pos id
    Just t -> do
      let t_e = TInt Nothing
      if not $ sameType t t_e then
        throwError $ TypeMismatch pos t_e t
      else
        typeCheckStmts stmts

typeCheckStmts (SDecr pos id : stmts) = typeCheckStmts (SIncr pos id : stmts)

typeCheckStmts (SRet pos e : stmts) = do -- TODO
  t <- typeCheckExpr e
  t' <- typeCheckStmts stmts
  if sameType t t' then
    pure t
  else
    throwError $ ReturnTypeMismatch pos [t, t']

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
        throwError $ ReturnTypeMismatch pos [t1, t2]
    _ -> do
      throwError $ TypeMismatch pos (TBool Nothing) t

typeCheckStmts (SCondElse pos e block block': stmts) = do
  t <- typeCheckExpr e
  case t of
    TBool _ -> do
      t1 <- typeCheckBlock block
      t2 <- typeCheckBlock block'
      t3 <- typeCheckStmts stmts
      if sameType t1 t2 && sameType t2 t3 then
        if not (isTAuto t1) && not (isTAuto t2) then pure t1
        else pure t3
      else
        throwError $ ReturnTypeMismatch pos [t1, t2, t3]
    _ -> do
      throwError $ TypeMismatch pos (TBool Nothing) t

typeCheckStmts (SWhile pos e block : stmts) = do
  t <- typeCheckExpr e
  case t of
    TBool _ -> do
      t1 <- typeCheckBlock block
      t2 <- typeCheckStmts stmts
      if sameType t1 t2 then
        pure t2
      else
        throwError $ ReturnTypeMismatch pos [t1, t2]
    _ -> do
      throwError $ TypeMismatch pos (TBool Nothing) t

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
    _ -> throwError $ TypeMismatchOptions pos [TInt Nothing, TBool Nothing, TStr Nothing] t

typeCheckStmts [] = pure $ TAuto Nothing



typeCheckExpr :: Expr -> TypeMonad
typeCheckExpr (EVar pos id) = do
  env <- ask
  let maybeType = Map.lookup id env
  case maybeType of
    Nothing -> throwError $ NotInScope pos id
    Just t -> pure t

typeCheckExpr (EApp pos id es) = do
  env <- ask
  ts <- mapM typeCheckExpr es
  let maybeType = Map.lookup id env
  case maybeType of
    Nothing -> throwError $ NotInScope pos id
    Just t@(TFun pos' t_args t') -> do
      if length t_args == length ts then do
        checkArgumentTypes pos id t ts
        checkRefArguments pos id t es
        pure t'
      else
        throwError $ FunctionWrongNumberOfArguments pos id t (length t_args) (length ts)
    Just (TPrint _) -> do
      if length ts == 1 then do
        let t' = head ts
        case t' of
          TInt _ -> pure $ TVoid pos
          TBool _ -> pure $ TVoid pos
          TStr _ -> pure $ TVoid pos
          _ -> throwError $ TypeMismatchOptions pos [TBool Nothing, TInt Nothing, TStr Nothing] t'
      else
        throwError $ FunctionWrongNumberOfArguments pos id (TPrint Nothing) 1 (length ts)
    Just t -> throwError $ NotAFunction pos id t

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
    _ -> throwError $ TypeMismatch pos (TBool Nothing) t

typeCheckExpr (ENot pos e) = do
  t <- typeCheckExpr e
  case t of
    TBool pos -> pure t
    _ -> throwError $ TypeMismatch pos (TBool Nothing) t

typeCheckExpr (EMul pos e op e') = do
  t <- typeCheckExpr e
  t' <- typeCheckExpr e'
  case t of
    TInt _ -> case t' of
      TInt _ -> pure $ TInt pos
      _ -> throwError $ TypeMismatch pos (TInt Nothing) t'
    _ -> throwError $ TypeMismatch pos (TInt Nothing) t

typeCheckExpr (EAdd pos e op e') = typeCheckExpr (EMul pos e (OTimes pos) e')

typeCheckExpr (ERel pos e op e') = do
  t <- typeCheckExpr e
  t' <- typeCheckExpr e'
  if not $ sameType t t' then
    throwError $ TypeMismatch pos t t'
  else
    case (t, t') of
      (TInt _, TInt _) -> pure $ TBool pos
      (TBool _, TBool _) ->
        case op of
          OEQU _ -> pure $ TBool pos
          ONE _ -> pure $ TBool pos
          _ -> throwError $ TypeMismatch pos (TInt Nothing) t
      (TStr _, TStr _) ->
        case op of
          OEQU _ -> pure $ TBool pos
          ONE _ -> pure $ TBool pos
          _ -> throwError $ TypeMismatch pos (TInt Nothing) t
      _ -> throwError $ TypeMismatchOptions pos [TBool Nothing, TInt Nothing, TStr Nothing] t

typeCheckExpr (EAnd pos e e') = do
  t <- typeCheckExpr e
  t' <- typeCheckExpr e'
  case t of
    TBool _ -> case t' of
      TBool _ -> pure $ TBool pos
      _ -> throwError $ TypeMismatch pos (TBool Nothing) t'
    _ -> throwError $ TypeMismatch pos (TBool Nothing) t

typeCheckExpr (EOr pos e e') = typeCheckExpr (EAnd pos e e')

typeCheckExpr (ELambdaBlock pos args t block) = do
  env <- ask
  checkVoidArguments args
  checkAutoArguments args
  let t'' = if isTFunWithTAuto t then TAuto pos else t
  t' <- local (createFunctionEnv args) (typeCheckBlock block)

  if (sameType t t' && not (isTAuto t')) || (isTAuto t' && not (isTAuto t)) then do
    let t_real = if not (isTAuto t'') then t else t'
        t_fun' = TFun pos (map fromArgToTArg args) t_real
    pure t_fun'
  else if isTAuto t && isTAuto t' then
    throwError $ TypeDeductionFailure pos
  else
    throwError $ TypeMismatch pos t t'

typeCheckExpr (ELambdaExpr pos args t e) = typeCheckExpr (ELambdaBlock pos args t (SBlock pos [SRet pos e]))