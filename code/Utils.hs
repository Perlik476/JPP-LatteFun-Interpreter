module Utils (showPos) where

import Prelude
import System.Environment ( getArgs )
import System.Exit
import Control.Monad      ( when )

import AbsLatteFun

showPos :: BNFC'Position -> String
showPos (Just (line, col)) = "line " ++ show line ++ ", column " ++ show col
showPos Nothing = "unknown location"