-- File generated by the BNF Converter (bnfc 2.9.4.1).

{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

-- | The abstract syntax of language LatteFun.

module AbsLatteFun where

import Prelude (Integer, String, Bool)
import qualified Prelude as C
  ( Eq, Ord, Show, Read
  , Functor, Foldable, Traversable
  , Int, Maybe(..)
  )
import qualified Data.String
import qualified Data.Map as Map

type Program = Program' BNFC'Position
data Program' a = PProgram a [Init' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Init = Init' BNFC'Position
data Init' a
    = IFnDef a (Type' a) Ident [Arg' a] (Block' a)
    | IVarDef a (Type' a) Ident (Expr' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Arg = Arg' BNFC'Position
data Arg' a = CopyArg a (Type' a) Ident | RefArg a (Type' a) Ident
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Block = Block' BNFC'Position
data Block' a = SBlock a [Stmt' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Stmt = Stmt' BNFC'Position
data Stmt' a
    = SEmpty a
    | SBStmt a (Block' a)
    | SDecl a (Type' a) Ident
    | SInit a (Init' a)
    | SAss a Ident (Expr' a)
    | SIncr a Ident
    | SDecr a Ident
    | SRet a (Expr' a)
    | SVRet a
    | SCond a (Expr' a) (Block' a)
    | SCondElse a (Expr' a) (Block' a) (Block' a)
    | SWhile a (Expr' a) (Block' a)
    | SExp a (Expr' a)
    | SPrint a (Expr' a)
    | SPrintln a (Expr' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Type = Type' BNFC'Position
data Type' a
    = TInt a | TStr a | TBool a | TVoid a | TFun a [TArg' a] (Type' a) | TAuto a | TPrint
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type TArg = TArg' BNFC'Position
data TArg' a = TCopyArg a (Type' a) | TRefArg a (Type' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Expr = Expr' BNFC'Position
data Expr' a
    = EVar a Ident
    | ELitInt a Integer
    | ELitTrue a
    | ELitFalse a
    | EApp a Ident [Expr' a]
    | EAppLambda a (Expr' a) [Expr' a]
    | EString a String
    | ENeg a (Expr' a)
    | ENot a (Expr' a)
    | EMul a (Expr' a) (MulOp' a) (Expr' a)
    | EAdd a (Expr' a) (AddOp' a) (Expr' a)
    | ERel a (Expr' a) (RelOp' a) (Expr' a)
    | EAnd a (Expr' a) (Expr' a)
    | EOr a (Expr' a) (Expr' a)
    | ELambdaExpr a [Arg' a] (Type' a) (Expr' a)
    | ELambdaBlock a [Arg' a] (Type' a) (Block' a)
    | EVal a Value
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

data Value = VInt Integer | VString String | VBool Bool | VFun Type [Arg] Block Env | VVoid | VNothing --VFun Type [Arg] Block Env State
  deriving (C.Eq, C.Ord, C.Show, C.Read)

type Var = Ident
type Env = Map.Map Var Loc
type Store = Map.Map Loc Value
type Loc = Integer
type TEnv = Map.Map Var Type

type AddOp = AddOp' BNFC'Position
data AddOp' a = OPlus a | OMinus a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type MulOp = MulOp' BNFC'Position
data MulOp' a = OTimes a | ODiv a | OMod a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type RelOp = RelOp' BNFC'Position
data RelOp' a = OLTH a | OLE a | OGTH a | OGE a | OEQU a | ONE a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

newtype Ident = Ident String
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)

-- | Start position (line, column) of something.

type BNFC'Position = C.Maybe (C.Int, C.Int)

pattern BNFC'NoPosition :: BNFC'Position
pattern BNFC'NoPosition = C.Nothing

pattern BNFC'Position :: C.Int -> C.Int -> BNFC'Position
pattern BNFC'Position line col = C.Just (line, col)

-- | Get the start position of something.

class HasPosition a where
  hasPosition :: a -> BNFC'Position

instance HasPosition Program where
  hasPosition = \case
    PProgram p _ -> p

instance HasPosition Init where
  hasPosition = \case
    IFnDef p _ _ _ _ -> p
    IVarDef p _ _ _ -> p

instance HasPosition Arg where
  hasPosition = \case
    CopyArg p _ _ -> p
    RefArg p _ _ -> p

instance HasPosition Block where
  hasPosition = \case
    SBlock p _ -> p

instance HasPosition Stmt where
  hasPosition = \case
    SEmpty p -> p
    SBStmt p _ -> p
    SDecl p _ _ -> p
    SInit p _ -> p
    SAss p _ _ -> p
    SIncr p _ -> p
    SDecr p _ -> p
    SRet p _ -> p
    SVRet p -> p
    SCond p _ _ -> p
    SCondElse p _ _ _ -> p
    SWhile p _ _ -> p
    SExp p _ -> p
    SPrint p _ -> p
    SPrintln p _ -> p

instance HasPosition Type where
  hasPosition = \case
    TInt p -> p
    TStr p -> p
    TBool p -> p
    TVoid p -> p
    TFun p _ _ -> p
    TAuto p -> p
    TPrint -> C.Nothing

instance HasPosition TArg where
  hasPosition = \case
    TCopyArg p _ -> p
    TRefArg p _ -> p

instance HasPosition Expr where
  hasPosition = \case
    EVar p _ -> p
    ELitInt p _ -> p
    ELitTrue p -> p
    ELitFalse p -> p
    EApp p _ _ -> p
    EAppLambda p _ _ -> p
    EString p _ -> p
    ENeg p _ -> p
    ENot p _ -> p
    EMul p _ _ _ -> p
    EAdd p _ _ _ -> p
    ERel p _ _ _ -> p
    EAnd p _ _ -> p
    EOr p _ _ -> p
    ELambdaExpr p _ _ _ -> p
    ELambdaBlock p _ _ _ -> p
    EVal p _ -> p

instance HasPosition AddOp where
  hasPosition = \case
    OPlus p -> p
    OMinus p -> p

instance HasPosition MulOp where
  hasPosition = \case
    OTimes p -> p
    ODiv p -> p
    OMod p -> p

instance HasPosition RelOp where
  hasPosition = \case
    OLTH p -> p
    OLE p -> p
    OGTH p -> p
    OGE p -> p
    OEQU p -> p
    ONE p -> p
