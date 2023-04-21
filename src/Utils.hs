module Utils where

import Prelude
import System.Environment ( getArgs )
import System.Exit
import Control.Monad      ( when )
import AbsLatteFun

import qualified Data.Map as Map
import qualified Data.Array.IO as Array

data Value
  = VInt Integer 
  | VString String 
  | VBool Bool 
  | VFun Type [Arg] Block Env 
  | VArr Type Arr
  | VVoid 
  | VNothing
  deriving (Eq)

type Var = Ident
type Env = Map.Map Var Loc
type Store = Map.Map Loc Value
type Loc = Integer
type TEnv = Map.Map Var Type
type Arr = Array.IOArray Int Value

showPos :: BNFC'Position -> String
showPos (Just (line, col)) = "line " ++ show line ++ ", column " ++ show col
showPos Nothing = "unknown location"