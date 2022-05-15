module InterpretImper
where

import qualified Data.Map as M

import Control.Monad.Except
import Control.Monad.State

import AbsImper
import ErrorImper

interpret :: Program -> IO()
interpret p =
    case execProgram p of
        Right output -> putStrLn output
        Left er -> putStr "Error:\t" >> putStrLn er

data 

type Store = M.Map Loc -> 
type VarEnv = M.Map Ident VarType
type FunEnv = M.Map Ident FunType
newtype Global = Global {
        funEnv :: FunTypeEnv,
        varEnv :: VarTypeEnv,
        insideLoop :: Bool,
        insideFun :: Bool
    }

emptyTypeEnv = TypeEnv {
    funEnv = M.empty,
    varEnv = M.empty,
    insideLoop = False,
    insideFun = False
}

type VarType = VarType' BNFC'Position
-- The type and is the variable read-only
data VarType' a = VarT {
        varTypeOf :: (Type' a),
        varIsReadonly :: Bool
    } deriving (Eq, Ord, Show, Read)

type FunType = FunType' BNFC'Position
-- First is the returned type, the rest are the parameters
data FunType' a = FunT (Type' a) [Type' a]
  deriving (Eq, Ord, Show, Read)

type MyMonad = ExceptT String (State Global)