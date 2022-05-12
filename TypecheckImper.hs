module TypecheckImper
where

import qualified Data.Map as M

import Control.Monad.Except
import Control.Monad.Reader

import AbsImper

typeCheck :: Program -> IO()
typeCheck p =
    case typeOfProgram p of
        Right t -> show t -- Tutaj mogę zwrócić monadę dla interpretera
        Left er -> putStrLn "Error:" >> putStrLn er

type VarTypeEnv = M.Map Ident VarType
type FunTypeEnv = M.Map Ident FunType
data TypeEnv = TypeEnv { funEnv :: FunTypeEnv, varEnv :: VarTypeEnv }

type VarType = VarType' BNFC'Position
-- The type and is the variable read-only
data VarType' a = VarT (Type' a) Data.Bool

type FunType = FunType' BNFC'Position
-- First is the returned type, the rest are the parameters
data FunType' a = FunT (Type' a) [Type' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type MyMonad = ExceptT String (Reader TypeEnv)

typeOfProgram :: Program -> Either String Type
typeOfProgram p = runReader (runExceptT (typeOfProg p)) M.empty

typeOfProg :: Program -> MyMonad Type
typeOfProg (Prog _ pstmts) = typeOfProgStmts pstmts

typeOfPstmts :: [ProgStmt] -> MyMonad Type
typeOfPstmts (p:ps) = (typeOfPstmt p) >> (typeOfPstmts ps)
typeOfPstmts [] = return

typeOfPstmt :: ProgStmt -> MyMonad Type
typeOfPstmt (ProgSt _ stmt) = typeOfStmt stmt
typeOfPstmt (FnDef declpos fname args block) = do
     

