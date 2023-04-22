-- -*- haskell -*- File generated by the BNF Converter (bnfc 2.9.4.1).

-- Parser definition for use with Happy
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module ParLatteFun
  ( happyError
  , myLexer
  , pProgram
  ) where

import Prelude

import qualified AbsLatteFun
import LexLatteFun

}

%name pProgram_internal Program
-- no lexer declaration
%monad { Err } { (>>=) } { return }
%tokentype {Token}
%token
  '!'      { PT _ (TS _ 1)  }
  '!='     { PT _ (TS _ 2)  }
  '%'      { PT _ (TS _ 3)  }
  '&&'     { PT _ (TS _ 4)  }
  '('      { PT _ (TS _ 5)  }
  ')'      { PT _ (TS _ 6)  }
  '*'      { PT _ (TS _ 7)  }
  '+'      { PT _ (TS _ 8)  }
  '++'     { PT _ (TS _ 9)  }
  ','      { PT _ (TS _ 10) }
  '-'      { PT _ (TS _ 11) }
  '--'     { PT _ (TS _ 12) }
  '->'     { PT _ (TS _ 13) }
  '.'      { PT _ (TS _ 14) }
  '/'      { PT _ (TS _ 15) }
  ';'      { PT _ (TS _ 16) }
  '<'      { PT _ (TS _ 17) }
  '<='     { PT _ (TS _ 18) }
  '='      { PT _ (TS _ 19) }
  '=='     { PT _ (TS _ 20) }
  '>'      { PT _ (TS _ 21) }
  '>='     { PT _ (TS _ 22) }
  '['      { PT _ (TS _ 23) }
  ']'      { PT _ (TS _ 24) }
  'auto'   { PT _ (TS _ 25) }
  'bool'   { PT _ (TS _ 26) }
  'else'   { PT _ (TS _ 27) }
  'false'  { PT _ (TS _ 28) }
  'if'     { PT _ (TS _ 29) }
  'int'    { PT _ (TS _ 30) }
  'lambda' { PT _ (TS _ 31) }
  'ref'    { PT _ (TS _ 32) }
  'return' { PT _ (TS _ 33) }
  'string' { PT _ (TS _ 34) }
  'true'   { PT _ (TS _ 35) }
  'void'   { PT _ (TS _ 36) }
  'while'  { PT _ (TS _ 37) }
  '{'      { PT _ (TS _ 38) }
  '||'     { PT _ (TS _ 39) }
  '}'      { PT _ (TS _ 40) }
  'λ'      { PT _ (TS _ 41) }
  L_Ident  { PT _ (TV _)    }
  L_integ  { PT _ (TI _)    }
  L_quoted { PT _ (TL _)    }

%%

Ident :: { (AbsLatteFun.BNFC'Position, AbsLatteFun.Ident) }
Ident  : L_Ident { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.Ident (tokenText $1)) }

Integer :: { (AbsLatteFun.BNFC'Position, Integer) }
Integer  : L_integ  { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), (read (tokenText $1)) :: Integer) }

String  :: { (AbsLatteFun.BNFC'Position, String) }
String   : L_quoted { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), ((\(PT _ (TL s)) -> s) $1)) }

Program :: { (AbsLatteFun.BNFC'Position, AbsLatteFun.Program) }
Program
  : ListInit { (fst $1, AbsLatteFun.PProgram (fst $1) (snd $1)) }

Init :: { (AbsLatteFun.BNFC'Position, AbsLatteFun.Init) }
Init
  : Type Ident '(' ListArg ')' Block { (fst $1, AbsLatteFun.IFnDef (fst $1) (snd $1) (snd $2) (snd $4) (snd $6)) }
  | Type Ident '=' Expr ';' { (fst $1, AbsLatteFun.IVarDef (fst $1) (snd $1) (snd $2) (snd $4)) }

ListInit :: { (AbsLatteFun.BNFC'Position, [AbsLatteFun.Init]) }
ListInit
  : Init { (fst $1, (:[]) (snd $1)) }
  | Init ListInit { (fst $1, (:) (snd $1) (snd $2)) }

Arg :: { (AbsLatteFun.BNFC'Position, AbsLatteFun.Arg) }
Arg
  : Type Ident { (fst $1, AbsLatteFun.CopyArg (fst $1) (snd $1) (snd $2)) }
  | Type 'ref' Ident { (fst $1, AbsLatteFun.RefArg (fst $1) (snd $1) (snd $3)) }

ListArg :: { (AbsLatteFun.BNFC'Position, [AbsLatteFun.Arg]) }
ListArg
  : {- empty -} { (AbsLatteFun.BNFC'NoPosition, []) }
  | Arg { (fst $1, (:[]) (snd $1)) }
  | Arg ',' ListArg { (fst $1, (:) (snd $1) (snd $3)) }

Block :: { (AbsLatteFun.BNFC'Position, AbsLatteFun.Block) }
Block
  : '{' ListStmt '}' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.SBlock (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1)) (snd $2)) }

ListStmt :: { (AbsLatteFun.BNFC'Position, [AbsLatteFun.Stmt]) }
ListStmt
  : {- empty -} { (AbsLatteFun.BNFC'NoPosition, []) }
  | Stmt ListStmt { (fst $1, (:) (snd $1) (snd $2)) }

Stmt :: { (AbsLatteFun.BNFC'Position, AbsLatteFun.Stmt) }
Stmt
  : ';' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.SEmpty (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1))) }
  | Block { (fst $1, AbsLatteFun.SBStmt (fst $1) (snd $1)) }
  | Type Ident ';' { (fst $1, AbsLatteFun.SDecl (fst $1) (snd $1) (snd $2)) }
  | Init { (fst $1, AbsLatteFun.SInit (fst $1) (snd $1)) }
  | Ident '=' Expr ';' { (fst $1, AbsLatteFun.SAss (fst $1) (snd $1) (snd $3)) }
  | Ident '++' ';' { (fst $1, AbsLatteFun.SIncr (fst $1) (snd $1)) }
  | Ident '--' ';' { (fst $1, AbsLatteFun.SDecr (fst $1) (snd $1)) }
  | 'return' Expr ';' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.SRet (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1)) (snd $2)) }
  | 'return' ';' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.SVRet (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1))) }
  | 'if' '(' Expr ')' Block { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.SCond (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1)) (snd $3) (snd $5)) }
  | 'if' '(' Expr ')' Block 'else' Block { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.SCondElse (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1)) (snd $3) (snd $5) (snd $7)) }
  | 'while' '(' Expr ')' Block { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.SWhile (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1)) (snd $3) (snd $5)) }
  | Expr ';' { (fst $1, AbsLatteFun.SExp (fst $1) (snd $1)) }

Type :: { (AbsLatteFun.BNFC'Position, AbsLatteFun.Type) }
Type
  : 'int' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.TInt (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1))) }
  | 'string' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.TStr (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1))) }
  | 'bool' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.TBool (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1))) }
  | 'void' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.TVoid (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1))) }
  | '[' '(' ListTArg ')' '->' Type ']' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.TFun (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1)) (snd $3) (snd $6)) }
  | 'auto' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.TAuto (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1))) }

TArg :: { (AbsLatteFun.BNFC'Position, AbsLatteFun.TArg) }
TArg
  : Type { (fst $1, AbsLatteFun.TCopyArg (fst $1) (snd $1)) }
  | Type 'ref' { (fst $1, AbsLatteFun.TRefArg (fst $1) (snd $1)) }

ListTArg :: { (AbsLatteFun.BNFC'Position, [AbsLatteFun.TArg]) }
ListTArg
  : {- empty -} { (AbsLatteFun.BNFC'NoPosition, []) }
  | TArg { (fst $1, (:[]) (snd $1)) }
  | TArg ',' ListTArg { (fst $1, (:) (snd $1) (snd $3)) }

ListType :: { (AbsLatteFun.BNFC'Position, [AbsLatteFun.Type]) }
ListType
  : {- empty -} { (AbsLatteFun.BNFC'NoPosition, []) }
  | Type { (fst $1, (:[]) (snd $1)) }
  | Type ',' ListType { (fst $1, (:) (snd $1) (snd $3)) }

Expr6 :: { (AbsLatteFun.BNFC'Position, AbsLatteFun.Expr) }
Expr6
  : Ident { (fst $1, AbsLatteFun.EVar (fst $1) (snd $1)) }
  | Integer { (fst $1, AbsLatteFun.ELitInt (fst $1) (snd $1)) }
  | 'true' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.ELitTrue (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1))) }
  | 'false' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.ELitFalse (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1))) }
  | Ident '(' ListExpr ')' { (fst $1, AbsLatteFun.EApp (fst $1) (snd $1) (snd $3)) }
  | '(' Expr ')' '(' ListExpr ')' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.EAppLambda (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1)) (snd $2) (snd $5)) }
  | String { (fst $1, AbsLatteFun.EString (fst $1) (snd $1)) }
  | '(' Expr ')' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), (snd $2)) }

Expr5 :: { (AbsLatteFun.BNFC'Position, AbsLatteFun.Expr) }
Expr5
  : '-' Expr6 { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.ENeg (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1)) (snd $2)) }
  | '!' Expr6 { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.ENot (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1)) (snd $2)) }
  | Expr6 { (fst $1, (snd $1)) }

Expr4 :: { (AbsLatteFun.BNFC'Position, AbsLatteFun.Expr) }
Expr4
  : Expr4 MulOp Expr5 { (fst $1, AbsLatteFun.EMul (fst $1) (snd $1) (snd $2) (snd $3)) }
  | Expr5 { (fst $1, (snd $1)) }

Expr3 :: { (AbsLatteFun.BNFC'Position, AbsLatteFun.Expr) }
Expr3
  : Expr3 AddOp Expr4 { (fst $1, AbsLatteFun.EAdd (fst $1) (snd $1) (snd $2) (snd $3)) }
  | Expr4 { (fst $1, (snd $1)) }

Expr2 :: { (AbsLatteFun.BNFC'Position, AbsLatteFun.Expr) }
Expr2
  : Expr2 RelOp Expr3 { (fst $1, AbsLatteFun.ERel (fst $1) (snd $1) (snd $2) (snd $3)) }
  | Expr3 { (fst $1, (snd $1)) }

Expr1 :: { (AbsLatteFun.BNFC'Position, AbsLatteFun.Expr) }
Expr1
  : Expr2 '&&' Expr1 { (fst $1, AbsLatteFun.EAnd (fst $1) (snd $1) (snd $3)) }
  | Expr2 { (fst $1, (snd $1)) }

Expr :: { (AbsLatteFun.BNFC'Position, AbsLatteFun.Expr) }
Expr
  : Expr1 '||' Expr { (fst $1, AbsLatteFun.EOr (fst $1) (snd $1) (snd $3)) }
  | 'lambda' '(' ListArg ')' '->' Type '.' Expr { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.ELambdaExpr (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1)) (snd $3) (snd $6) (snd $8)) }
  | 'λ' '(' ListArg ')' '->' Type '.' Expr { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.ELambdaExpr (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1)) (snd $3) (snd $6) (snd $8)) }
  | 'lambda' '(' ListArg ')' '->' Type Block { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.ELambdaBlock (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1)) (snd $3) (snd $6) (snd $7)) }
  | 'λ' '(' ListArg ')' '->' Type Block { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.ELambdaBlock (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1)) (snd $3) (snd $6) (snd $7)) }
  | Expr1 { (fst $1, (snd $1)) }

ListExpr :: { (AbsLatteFun.BNFC'Position, [AbsLatteFun.Expr]) }
ListExpr
  : {- empty -} { (AbsLatteFun.BNFC'NoPosition, []) }
  | Expr { (fst $1, (:[]) (snd $1)) }
  | Expr ',' ListExpr { (fst $1, (:) (snd $1) (snd $3)) }

AddOp :: { (AbsLatteFun.BNFC'Position, AbsLatteFun.AddOp) }
AddOp
  : '+' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.OPlus (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1))) }
  | '-' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.OMinus (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1))) }

MulOp :: { (AbsLatteFun.BNFC'Position, AbsLatteFun.MulOp) }
MulOp
  : '*' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.OTimes (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1))) }
  | '/' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.ODiv (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1))) }
  | '%' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.OMod (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1))) }

RelOp :: { (AbsLatteFun.BNFC'Position, AbsLatteFun.RelOp) }
RelOp
  : '<' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.OLTH (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1))) }
  | '<=' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.OLE (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1))) }
  | '>' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.OGTH (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1))) }
  | '>=' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.OGE (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1))) }
  | '==' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.OEQU (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1))) }
  | '!=' { (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1), AbsLatteFun.ONE (uncurry AbsLatteFun.BNFC'Position (tokenLineCol $1))) }

{

type Err = Either String

happyError :: [Token] -> Err a
happyError ts = Left $
  "syntax error at " ++ tokenPos ts ++
  case ts of
    []      -> []
    [Err _] -> " due to lexer error"
    t:_     -> " before `" ++ (prToken t) ++ "'"

myLexer :: String -> [Token]
myLexer = tokens

-- Entrypoints

pProgram :: [Token] -> Err AbsLatteFun.Program
pProgram = fmap snd . pProgram_internal
}
