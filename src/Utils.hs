module Utils where

import Prelude
import System.Environment ( getArgs )
import System.Exit
import Control.Monad      ( when )
import AbsLatteFun

import qualified Data.Map as Map

data Value = VInt Integer | VString String | VBool Bool | VFun Type [Arg] Block Env | VVoid | VNothing
  deriving (Eq, Ord, Show, Read)

type Var = Ident
type Env = Map.Map Var Loc
type Store = Map.Map Loc Value
type Loc = Integer
type TEnv = Map.Map Var Type

showPos :: BNFC'Position -> String
showPos (Just (line, col)) = "line " ++ show line ++ ", column " ++ show col
showPos Nothing = "unknown location"