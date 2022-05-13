module TypecheckImper
where

import qualified Data.Map as M

import Control.Monad.Except
import Control.Monad.State

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

varIsReadonly :: VarType -> Data.Bool
varIsReadonly (VarT _ b) = b

type FunType = FunType' BNFC'Position
-- First is the returned type, the rest are the parameters
data FunType' a = FunT (Type' a) [Type' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type MyMonad = ExceptT String (State TypeEnv)

typeOfProgram :: Program -> Either String Type
typeOfProgram p = evalState (runExceptT (typeOfProg p)) M.empty

typeOfProg :: Program -> MyMonad Type
typeOfProg (Prog _ pstmts) = typeOfProgStmts pstmts

typeOfPstmts :: [ProgStmt] -> MyMonad Type
typeOfPstmts (p:ps) = (typeOfPstmt p) >> (typeOfPstmts ps)
typeOfPstmts [] = return ()

typeOfPstmt :: ProgStmt -> MyMonad Type
typeOfPstmt (ProgSt _ stmt) = typeOfStmt stmt
typeOfPstmt (FnDef _ retType fname args block) = do
    s <- get
    _addArgs args
    s' <- get
    put $ _appendFunction fname ftype s'
    realRetT <- inferTypeOfBlock block retType
    put $ _appendFunction fname ftype s
    if realRetT == retType
        then return realRetT
        else throwError $ errorFunType fname ftype
  where
      ftype = FunT retType $ _argsToTypes args


-- check if the types are correct inside the block
-- and the only type that can be returned matches the parameter Type
inferTypeOfBlock :: Block -> Type -> MyMonad (Maybe Type)
inferTypeOfBlock (StBlock pos stmts) infType = do
    s <- get
    retType <- inferTypeReturn stmts infType Nothing
    put s
    return retType

inferTypeReturn :: [Stmt] -> Type -> Maybe Type -> MyMonad (Maybe Type)
inferTypeReturn (s:st) inferType retType =
    inferTypeReturnSingle s infType retType >>= inferTypeReturn st infType
inferTypeReturn [] _ retType = return retType

inferTypeReturnSingle :: Stmt -> Type -> Maybe Type -> MyMonad (Maybe Type)
inferTypeReturnSingle st infType retType =
    typeOfStmt st >> inferReturnedType st infType retType

inferReturnedType :: Stmt -> Type -> Maybe Type -> MyMonad (Maybe Type)
inferReturnedType (Ret pos expr) infType retType = do
    exprType <- typeOfExpr expr
    if exprType == infType
        then return $ Just exprType
        else throwError $ errorFunTypeReturn pos infType exprType

inferReturnedType (Cond _ ifBlock elifBlocks) infType retType =
    inferReturnedTypeIf ifBlock infType retType >>=
        inferReturnedTypeElifs elifBlocks infType

inferReturnedType (CondElse _ ifBlock elifBlocks elseBlock) infType retType =
    inferReturnedTypeIf ifBlock infType retType >>=
        inferReturnedTypeElifs elifBlocks infType >>=
            inferReturnedTypeElse elseBlock infType

inferReturnedType f@(For _ roAss endValExpr )

condTrue :: Expr
condTrue = ELitTrue BNFC'NoPosition

inferReturnedTypeIf :: IfBl -> Type -> Maybe Type -> MyMonad (Maybe Type)
inferReturnedTypeIf (IfBlock _ expr block) =
    inferReturnedTypeCond expr block

inferReturnedTypeElifs :: [ElifBl] -> Type -> Maybe Type -> MyMonad (Maybe Type)
inferReturnedTypeElifs (e:es) infType retType =
    inferReturnedTypeElif e infType retType >>= inferReturnedTypeElifs es infType
inferReturnedTypeElifs [] _ = return

inferReturnedTypeElif :: ElifBl -> Type -> Maybe Type -> MyMonad (Maybe Type)
inferReturnedTypeElif e@(ElifBlock _ expr block) =
    inferReturnedTypeCond expr block

inferReturnedTypeElse :: ElseBl -> Type -> Maybe Type -> MyMonad (Maybe Type)
inferReturnedTypeElse e@(ElseBlock _ block) =
    inferReturnedTypeCond condTrue block

inferReturnedTypeCond :: Expr -> Block -> Type -> Maybe Type -> MyMonad (Maybe Type)
inferReturnedTypeCond expr block infType retType = do
    typeOfCondBlock expr block
    blockType <- inferTypeOfBlock block infType
    case blockType of
        Nothing -> return retType
        _ -> return blockType

typeOfStmt :: Stmt -> MyMonad Type
typeOfStmt ...

_argsToTypes :: [Arg] -> [Type]
_argsToTypes = map _argToType

_argToType :: Arg -> Type
_argToType (FnArg _ t _) = t

_addArgs :: [Arg] -> MyMonad Type
_addArgs (a:as) = (_addArg a) >> (_addArgs as)
_addArgs [] = return ()

_addArg :: Arg -> MyMonad Type
_addArg (FnArg _ t argname) = _addVar argname t False

-- read-only variables cannot be overriden
_addVar :: Ident -> Type -> Data.Bool -> MyMonad Type
_addVar varname vartype isReadOnly = do
    s <- get
    let prevVar = M.lookup varname
    let action = put $ _appendVar varname (VarT vartype isReadOnly) s in
        case prevVar of
            Nothing -> action >> return vartype
            Just prevType ->
                if varIsReadonly prevType
                    then throwError $ errorROVarOverride prevType varType
                    else action >> return vartype


_appendFunction :: Ident -> FunType -> TypeEnv -> TypeEnv
_appendFunction fname ftype env =
    TypeEnv {
        funEnv = M.insert fname ftype $ funEnv env,
        varEnv = varEnv env}

_appendVar :: Ident -> VarType -> Data.Bool -> TypeEnv -> TypeEnv
_appendVar varname vartype env =
    TypeEnv {
        funEnv = funEnv env,
        varEnv = M.insert varname vartype $ varEnv env}


errorFunType :: Ident -> FunType -> String
errorFunType fname ftype =
    undefined


