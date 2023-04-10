module TypeChecker(typeCheck) where

import Prelude
import System.Environment ( getArgs )
import System.Exit
import Control.Monad      ( when )

import AbsLatteFun
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as Map
import Data.Maybe

type TypeMonad = ExceptT String (ReaderT TEnv IO) Type

showPos :: BNFC'Position -> String
showPos (Just (line, col)) = "line " ++ show line ++ ", column " ++ show col
showPos Nothing = "unknown location"

fromIdent :: Ident -> String
fromIdent (Ident s) = s

initTEnv :: TEnv
initTEnv = Map.insert (Ident "println") TPrint $ Map.insert (Ident "print") TPrint Map.empty


typeCheck :: Program -> IO Bool
typeCheck p = do
  result <- runReaderT (runExceptT (typeCheckProg p)) initTEnv
  case result of
    Left error -> do
      putStr "Static type checking failed.\n"
      putStr $ error ++ "\n"
      pure False
    Right _ -> pure True

typeCheckProg :: Program -> TypeMonad
typeCheckProg (PProgram pos inits) = do
  initsContainMain inits
  typeCheckStmts [SInit (getInitPos init) init | init <- inits]

initsContainMain :: [Init] -> TypeMonad
initsContainMain ((IVarDef pos _ id _) : inits) =
  if fromIdent id /= "main" then initsContainMain inits
  else throwError $ "Illegal toplevel variable name main at " ++ showPos pos
initsContainMain ((IFnDef pos t id args block) : inits) = do
  if fromIdent id /= "main" then initsContainMain inits
  else
    if not $ sameType t (TInt Nothing) then
      throwError $ "Function main at " ++ showPos pos ++ " should have return type int."
    else if not (null args) then
      throwError $ "Function main at " ++ showPos pos ++ " should have no arguments."
    else
      if any (\ini -> fromIdent (getInitId ini) == "main") inits then
        throwError "Multiple definitions of main in the toplevel."
      else
        pure t
initsContainMain [] = throwError "Function main is not defined."


getInitPos :: Init -> BNFC'Position
getInitPos (IVarDef pos _ _ _) = pos
getInitPos (IFnDef pos _ _ _ _) = pos

getInitId :: Init -> Ident
getInitId (IVarDef _ _ id _) = id
getInitId (IFnDef _ _ id _ _) = id

typeCheckBlock :: Block -> TypeMonad
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
showType' TPrint = "[(int | bool | string) -> void] (print)"

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
  isTAuto t_ret || foldr ((\t res -> res || isTAuto t) . fromTArgToType) False t_args
isTFunWithTAuto _ = False

isTAuto :: Type -> Bool
isTAuto (TAuto _) = True
isTAuto _ = False

fromArgToTArg :: Arg -> TArg
fromArgToTArg (CopyArg pos t _) = TCopyArg pos t
fromArgToTArg (RefArg pos t _) = TRefArg pos t

fromArgToId :: Arg -> Ident
fromArgToId (CopyArg _ _ id) = id
fromArgToId (RefArg _ _ id) = id

fromTArgToType :: TArg -> Type
fromTArgToType (TCopyArg _ t) = t
fromTArgToType (TRefArg _ t) = t

errorTypeMismatch :: BNFC'Position -> String -> String
errorTypeMismatch pos message = "Type mismatch at " ++ showPos pos ++ ".\n" ++ message ++ "."

errorDeclarationFailure :: BNFC'Position -> String -> String
errorDeclarationFailure pos message = "Declaration failure at " ++ showPos pos ++ ".\n" ++ message ++ "."

errorDeclarationFailureVariable :: BNFC'Position -> Ident -> String -> String
errorDeclarationFailureVariable pos var message = errorDeclarationFailure pos (".\nVariable " ++ fromIdent var ++ " " ++ message)

errorAssignmentFailureVoid :: BNFC'Position -> Ident -> String
errorAssignmentFailureVoid pos var = "Assignment failure at " ++ showPos pos ++ ".\nCannot assign void expression to variable " ++ fromIdent var ++ "."

errorNotInScope :: BNFC'Position -> Ident -> String
errorNotInScope pos var = "Reference before delaration at " ++ showPos pos ++ ".\nVariable " ++ fromIdent var ++ " not in scope" ++ "."

typeCheckStmts :: [Stmt] -> TypeMonad
typeCheckStmts (SEmpty pos : stmts) = typeCheckStmts stmts

typeCheckStmts (SBStmt pos block : stmts) = do
  typeCheckBlock block
  typeCheckStmts stmts

typeCheckStmts (SDecl pos t id : stmts) = do
  case t of
    TAuto _ -> throwError $ errorDeclarationFailure pos $ "Declared variable " ++ fromIdent id ++ " of auto type without initialization"
    TVoid _ -> throwError $ errorDeclarationFailure pos $ "Declared variable " ++ fromIdent id ++ " of void type"
    _ -> local (Map.insert id t) (typeCheckStmts stmts)

typeCheckStmts (SInit pos (IVarDef pos' t id e) : stmts) = do
  if isTVoid t then
    throwError $ errorDeclarationFailureVariable pos id "has type void"
  else if isTFunWithTAuto t then
    throwError $ errorDeclarationFailureVariable pos id "has functional type with auto argument or return value"
  else do
    t_e <- typeCheckExpr e
    if isTVoid t_e then
      throwError $ errorAssignmentFailureVoid pos id
    else if sameType t t_e || isTAuto t then
      local (Map.insert id t_e) (typeCheckStmts stmts)
    else
      throwError $ errorTypeMismatch pos $ showType t ++ " and " ++ showType t_e

typeCheckStmts (SInit pos (IFnDef pos' t id args block) : stmts) = do
  env <- ask
  let t_args = map (fromTArgToType . fromArgToTArg) args
      proper = foldr (\t' res -> res && not (isTAuto t') && not (isTVoid t') && not (isTFunWithTAuto t')) True t_args
      id_args = map fromArgToId args
  if not proper then
    throwError $ errorDeclarationFailureVariable pos id "argument type is void or contains auto"
  else do
    let env' = foldr (\(id', t') env'' -> Map.insert id' t' env'') env $ (id, t_fun):zip id_args t_args
        t_fun = TFun pos' (map fromArgToTArg args) t
    t' <- local (const env') (typeCheckBlock block)
    if (sameType t t' && not (isTAuto t')) || (isTAuto t' && not (isTAuto t)) then do
      let t_real = if not (isTAuto t) then t else t'
          t_fun' = TFun pos' (map fromArgToTArg args) t_real
          env'' = Map.insert id t_fun' env'
      local (const env'') (typeCheckStmts stmts)
    else
      throwError $
        if isTAuto t && isTAuto t' then
          errorDeclarationFailureVariable pos id "inferring of auto type failed in function definition"
        else
          errorTypeMismatch pos $ showType t ++ " and " ++ showType t'

typeCheckStmts (SAss pos id e : stmts) = do
  t_e <- typeCheckExpr e
  if isTVoid t_e then
    throwError $ errorAssignmentFailureVoid pos id
  else do
    env <- ask
    let maybeType = Map.lookup id env
    case maybeType of
      Nothing -> throwError $ errorNotInScope pos id
      Just t -> do
        if not $ sameType t t_e then
          throwError $ errorTypeMismatch pos ("Cannot assign expression of type " ++ showType t_e ++ " to variable "
                                              ++ fromIdent id ++ " of type " ++ showType t)
        else
          typeCheckStmts stmts

typeCheckStmts (SIncr pos id : stmts) = do
  env <- ask
  let maybeType = Map.lookup id env
  case maybeType of
    Nothing -> throwError $ errorNotInScope pos id
    Just t -> do
      let t_e = TInt pos
      if not $ sameType t t_e then
        throwError $ errorTypeMismatch pos $ showType t ++ " is not of type int"
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
        throwError $ errorTypeMismatch pos $ "Different return values in function definition: " ++ showType t1 ++ " and " ++ showType t2
    _ -> do
      throwError $ errorTypeMismatch pos $ showType t ++ " is not of type bool"

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
        throwError $ errorTypeMismatch pos "Different return values in function definition"
    _ -> do
      throwError $ errorTypeMismatch pos $ showType t ++ " is not of type bool"

typeCheckStmts (SWhile pos e block : stmts) = do
  t <- typeCheckExpr e
  case t of
    TBool _ -> do
      t1 <- typeCheckBlock block
      t2 <- typeCheckStmts stmts
      if sameType t1 t2 then
        pure t2
      else
        throwError $ errorTypeMismatch pos $ "Different return values in function definition: " ++ showType t1 ++ " and " ++ showType t2
    _ -> do
      throwError $ errorTypeMismatch pos $ showType t ++ " is not of type bool"

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
    _ -> throwError $ errorTypeMismatch pos $ showType t ++ " is not of basic type (bool/int/string)"


typeCheckStmts (SPrintln pos e : stmts) = typeCheckStmts (SPrint pos e : stmts)

typeCheckStmts [] = pure $ TAuto Nothing -- TODO?


checkArgumentTypes :: [Type] -> [Type] -> Maybe (Integer, Type, Type)
checkArgumentTypes = checkArgumentTypes' 1

checkArgumentTypes' :: Integer -> [Type] -> [Type] -> Maybe (Integer, Type, Type)
checkArgumentTypes' n (t:ts) (t':ts') =
  if sameType t t' then checkArgumentTypes' (n + 1) ts ts'
  else Just (n, t, t')
checkArgumentTypes' _ _ _ = Nothing

checkRefArguments :: [TArg] -> [Expr] -> Maybe Integer
checkRefArguments = checkRefArguments' 1

checkRefArguments' :: Integer -> [TArg] -> [Expr] -> Maybe Integer
checkRefArguments' n (t:ts) (e:es) =
  case t of
    TRefArg _ _ ->
      case e of
        EVar _ _ -> checkRefArguments' (n + 1) ts es
        _ -> Just n
    _ -> checkRefArguments' (n + 1) ts es
checkRefArguments' _ _ _ = Nothing


typeCheckExpr :: Expr -> TypeMonad
typeCheckExpr (EVar pos id) = do
  env <- ask
  let maybeType = Map.lookup id env
  case maybeType of
    Nothing -> throwError $ errorNotInScope pos id
    Just t -> pure t

typeCheckExpr (EApp pos id es) = do
  env <- ask
  ts <- mapM typeCheckExpr es
  let maybeType = Map.lookup id env
  case maybeType of
    Nothing -> throwError $ errorNotInScope pos id
    Just t@(TFun pos' t_args t') -> do
      if length t_args == length ts then
        case checkArgumentTypes (map fromTArgToType t_args) ts of
          Nothing ->
            case checkRefArguments t_args es of
              Nothing -> pure t'
              Just n ->
                throwError (errorTypeMismatch pos $ "Expected a variable as argument number " ++ show n
                  ++ " applied to the function " ++ fromIdent id ++ ", because it's a reference type")
          Just (n, t1, t2) ->
            throwError (errorTypeMismatch pos $ "Argument number " ++ show n ++ " applied to the function "
              ++ fromIdent id ++ " of type " ++ showType t ++ " is of type " ++ showType t2 ++ ", expected " ++ showType t1)
      else
        throwError (errorTypeMismatch pos $ "Inorrect number of arguments to function " ++ fromIdent id ++ " of type " ++ showType t ++ ". "
          ++ "Expected " ++ show (length t_args) ++ ", got " ++ show (length ts))
    Just TPrint -> do
      if length ts == 1 then do
        let t' = head ts
        case t' of
          TInt _ -> pure $ TVoid pos
          TBool _ -> pure $ TVoid pos
          TStr _ -> pure $ TVoid pos
          _ -> throwError $ errorTypeMismatch pos $ showType t' ++ " is not of basic type (bool/int/string)"
      else
        throwError $ errorTypeMismatch pos "Function print requires exactly one argument"
    Just t -> throwError $ errorTypeMismatch pos $ "Expected a function, got " ++ showType t

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
    _ -> throwError $ errorTypeMismatch pos $ "Expected int, got " ++ showType t

typeCheckExpr (ENot pos e) = do
  t <- typeCheckExpr e
  case t of
    TBool pos -> pure t
    _ -> throwError $ errorTypeMismatch pos $ "Expected bool, got " ++ showType t

typeCheckExpr (EMul pos e op e') = do
  t <- typeCheckExpr e
  t' <- typeCheckExpr e'
  case (t, t') of
    (TInt _, TInt _) -> pure $ TInt pos
    _ -> throwError $ errorTypeMismatch pos $ "Expected two ints, got " ++ showType t ++ " and " ++ showType t'

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
        _ -> throwError $ errorTypeMismatch pos $ "Expected two ints, got " ++ showType t ++ " and " ++ showType t'
    (TStr _, TStr _) ->
      case op of
        OEQU pos' -> pure $ TBool pos
        ONE pos' -> pure $ TBool pos
        _ -> throwError $ errorTypeMismatch pos $ "Expected two ints, got " ++ showType t ++ " and " ++ showType t'
    _ -> throwError $errorTypeMismatch pos $ "Expected two basic type expressions (int/bool/string), got " ++ showType t ++ " and " ++ showType t'

typeCheckExpr (EAnd pos e e') = do
  t <- typeCheckExpr e
  t' <- typeCheckExpr e'
  case (t, t') of
    (TBool _, TBool _) -> pure $ TBool pos
    _ -> throwError $ errorTypeMismatch pos $ "Expected two bools, got " ++ showType t ++ " and " ++ showType t'

typeCheckExpr (EOr pos e e') = typeCheckExpr (EAnd pos e e')

typeCheckExpr (ELambdaBlock pos args t block) = do
  env <- ask
  let t_args = map (fromTArgToType . fromArgToTArg) args
      proper = foldr (\t' res -> res && not (isTAuto t') && not (isTVoid t') && not (isTFunWithTAuto t')) True t_args
      id_args = map fromArgToId args
  if not proper then
    throwError $ errorDeclarationFailure pos "Argument type is void or contains auto"
  else do
    let t'' = if isTFunWithTAuto t then TAuto pos else t
    let env' = foldr (\(id', t') env'' -> Map.insert id' t' env'') env $ zip id_args t_args
        t_fun = TFun pos (map fromArgToTArg args) t''
    t' <- local (const env') (typeCheckBlock block)
    if (sameType t t' && not (isTAuto t')) || (isTAuto t' && not (isTAuto t)) then do
      let t_real = if not (isTAuto t'') then t else t'
          t_fun' = TFun pos (map fromArgToTArg args) t_real
      pure t_fun'
    else
      throwError $
        if isTAuto t && isTAuto t' then
          errorDeclarationFailure pos "inferring of auto type failed in function definition"
        else
          errorTypeMismatch pos $ showType t ++ " and " ++ showType t'

typeCheckExpr (ELambdaExpr pos args t e) = typeCheckExpr (ELambdaBlock pos args t (SBlock pos [SRet pos e]))

typeCheckExpr (EVal pos _) = pure $ TAuto pos