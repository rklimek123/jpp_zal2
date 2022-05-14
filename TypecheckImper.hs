module TypecheckImper
where

import qualified Data.Map as M
import qualified Data

import Control.Monad.Except
import Control.Monad.State

import AbsImper
import ErrorImper

typeCheck :: Program -> IO()
typeCheck p =
    case typeOfProgram p of
        Right t -> show t -- Tutaj mogę zwrócić monadę dla interpretera
        Left er -> putStrLn "Error: " >> putStrLn er

type VarTypeEnv = M.Map Ident VarType
type FunTypeEnv = M.Map Ident FunType
data TypeEnv = TypeEnv {
        funEnv :: FunTypeEnv,
        varEnv :: VarTypeEnv,
        insideLoop :: Data.Bool,
        insideFun :: Data.Bool
    }

type VarType = VarType' BNFC'Position
-- The type and is the variable read-only
data VarType' a = VarT {
        varTypeOf :: (Type' a),
        varIsReadonly :: Data.Bool
    }

type FunType = FunType' BNFC'Position
-- First is the returned type, the rest are the parameters
data FunType' a = FunT (Type' a) [Type' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type MyMonad = ExceptT String (State TypeEnv)

evalTypeProgram :: Program -> Either String Type
evalProgram p = execTypeProgram.execMyMonad

execMyMonad :: MyMonad Type -> Either String Type
execMyMonad m -> evalState (runExceptT m) M.empty

execTypeProgram :: Program -> MyMonad Type
execTypeProgram (Prog _ pstmts) = execTypePstmts pstmts (Void BNFC'NoPosition)

execTypePstmts :: [ProgStmt] -> Type -> MyMonad Type
execTypePstmts (p:ps) _ = (execTypePstmt p) >>= (execTypePstmts ps)
execTypePstmts [] = return


execTypePstmt :: ProgStmt -> MyMonad Type
execTypePstmt (ProgSt _ stmt) = execTypeStmt stmt
execTypePstmt (FnDef _ retType fname args block) = do
    s <- get

    _addArgs args
    s' <- get
    put $ _appendInFun True (_appendFunction fname ftype s')
    
    realRetT <- inferTypeOfBlock block retType
    
    put $ _appendFunction fname ftype s
    
    if realRetT == retType
        then return realRetT
        else throwError $ errorFunType fname retType realRetT
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

inferReturnedType f@(For _ roAss _ block) infType retType = do
    s <- get

    execTypeVarDecl True roAss
    put $ _appendInLoop True s

    infBlockRet <- inferReturnedTypeInBlock block infType retType
    
    put s
    return infBlockRet

inferReturnedType w@(While _ expr block) infType retType = do
    s <- get

    put $ _appendInLoop True s

    infBlockRet <- inferReturnedTypeInBlock block infType retType
    
    put s
    return infBlockRet

inferReturnedType st _ = execTypeSt st >> return

condTrue :: Expr
condTrue = ELitTrue BNFC'NoPosition

inferReturnedTypeIf :: IfBl -> Type -> Maybe Type -> MyMonad (Maybe Type)
inferReturnedTypeIf (IfBlock _ expr block) =
    inferReturnedTypeInBlock block

inferReturnedTypeElifs :: [ElifBl] -> Type -> Maybe Type -> MyMonad (Maybe Type)
inferReturnedTypeElifs (e:es) infType retType =
    inferReturnedTypeElif e infType retType >>= inferReturnedTypeElifs es infType
inferReturnedTypeElifs [] _ = return

inferReturnedTypeElif :: ElifBl -> Type -> Maybe Type -> MyMonad (Maybe Type)
inferReturnedTypeElif (ElifBlock _ _ block) =
    inferReturnedTypeInBlock block

inferReturnedTypeElse :: ElseBl -> Type -> Maybe Type -> MyMonad (Maybe Type)
inferReturnedTypeElse (ElseBlock _ block) =
    inferReturnedTypeInBlock block

inferReturnedTypeInBlock :: Block -> Type -> Maybe Type -> MyMonad (Maybe Type)
inferReturnedTypeInBlock block infType retType = do
    blockType <- inferTypeOfBlock block infType
    case blockType of
        Nothing -> return retType
        _ -> return blockType

execTypeStmts :: [Stmt] -> Type -> MyMonad Type
execTypeStmts (st:sts) _ = (execTypeStmt st) >>= (execTypeStmts sts)
execTypeStmts [] t = return t

execTypeStmt :: Stmt -> MyMonad Type
execTypeStmt (Decl _ assSt) = execTypeVarDecl False assSt

execTypeStmt (DeclRO _ assSt) = execTypeVarDecl True assSt

execTypeStmt (AssStmt _ assSt) = execTypeAss assSt

execTypeStmt (TupleAss _ tbox expr) = do
    exprType <- typeOfExpr expr
    s <- get
    let tboxType = _getTBoxType s tbox
    if exprType == tboxType
        then return exprType
        else throwError $ errorTupleType tBoxType expr

execTypeStmt (Cond _ ifBlock elifBlocks) =
    execTypeIf ifBlock >>= execTypeElifs elifBlocks

execTypeStmt (CondElse _ ifBlock elifBlocks elseBlock) =
    execTypeIf ifBlock >>= execTypeElifs elifBlocks >>= execTypeElse elseBlock

execTypeStmt (For _ roAss expr block) = do
    s <- get
    
    endType <- typeOfExpr expr
    if endType /= (Int BNFC'NoPosition)
        then throwError $ errorForIterType endType
    
    beginType <- execTypeVarDecl True roAss
    if beginType /= (Int BNFC'NoPosition)
        then throwError $ errorForIterType beginType

    put $ _appendInLoop True s

    blockType <- typeOfBlock block
    
    put s
    return blockType

execTypeStmt (While _ expr block) =
    execTypeCondBlock expr block

execTypeStmt (Ret pos expr) = do
    s <- get

    if !(insideFun s)
        then throwError $ errorRetOutsideFun pos
    
    typeOfExpr expr

execTypeStmt (Break pos) = execTypeJump True pos
execTypeStmt (Continue pos) = execTypeJump False pos

execTypeStmt (Print _ expr) = typeOfExpr expr

execTypeStmt (Skip _) = return (Void BNFC'NoPosition)

execTypeStmt (SExp _ expr) = typeOfExpr expr

execTypeVarDecl :: Data.Bool -> AStmt -> MyMonad Type
execTypeVarDecl isReadOnly (Ass _ varname expr) = do
    exprType <- typeOfExpr expr
    _addVar varname exprType isReadOnly

execTypeAss :: AStmt -> MyMonad Type
execTypeAss (Ass _ varname expr) = do
    exprType <- typeOfExpr expr
    _changeVar varname exprType

_getTBoxType :: TBox -> MyMonad Type
_getTBoxType env (TupleBox pos tElems) =
    return (Tuple pos $ _getTElemsType tElems)

_getTElemsType :: [TElem] -> MyMonad [Type]
_getTElemsType = mapM (_getTElemType env)

_getTElemType :: TElem -> MyMonad Type
_getTElemType (TupleTup _ tbox) =
    _getTBoxType env tbox

_getTElemType (TupleAtom pos varname) = do
    s <- get
    let mVartype = M.lookup varname $ varEnv s
    case mVartype of
        Nothing -> throwError $ errorVarNotExist pos varname
        Just vartype -> return vartype

_getTElemType (TupleIgn pos) =
    return (Polimorph pos)

execTypeIf :: IfBl -> MyMonad Type
execTypeIf (IfBlock _ expr block) = execTypeCondBlock expr block

execTypeElifs :: [ElifBl] -> Type -> MyMonad Type
execTypeElifs (e:es) _ =
    execTypeElif e >>= execTypeElifs es
execTypeElifs [] _ = return

execTypeElif :: ElifBl -> MyMonad Type
execTypeElif (ElifBlock _ expr block) = execTypeCondBlock expr block

execTypeElse :: ElseBl -> MyMonad Type
execTypeElse (ElseBlock block) = execTypeCondBlock condTrue block

execTypeCondBlock :: Expr -> Block -> MyMonad Type
execTypeCondBlock expr block = do
    exprType <- typeOfExpr expr
    if exprType /= (Bool BNFC'NoPosition)
        then throwError $ errorCondExprType exprType
    typeOfBlock block

execTypeJump :: Bool -> BNFC'Position -> MyMonad Type
execTypeJump isBreak pos = do
    s <- get

    if !(insideLoop s)
        then throwError $ errorJumpOutsideLoop isBreak pos
    
    return (Void BNFC'NoPosition)

typeOfStmt :: Stmt -> MyMonad Type
typeOfStmt st = do
    s <- get
    stType <- execTypeStmt st
    put s
    return stType

typeOfBlock :: Block -> MyMonad Type
typeOfBlock (StBlock _ stmts) = do
    s <- get
    retType <- execTypeStmts stmts (Void BNFC'NoPosition)
    put s
    return retType

typeOfExpr :: Expr -> MyMonad Type
typeOfExpr (EVar pos varname) = do
    s <- get
    let varT = M.lookup varname $ varEnv s
    case varT of
        Nothing -> throwError $ errorVarNotExist pos varname
        Just vartype -> return $ varTypeOf vartype

typeOfExpr (ELitInt pos _) = return $ Int pos
typeOfExpr (ELitTrue pos) = return $ Bool pos
typeOfExpr (ELitFalse pos) = return $ Bool pos

typeOfExpr (ELitTuple pos exprs) = do
    types <- mapM typeOfExpr exprs
    return $ Tuple pos types

typeOfExpr (EApp pos funname args) = do
    s <- get
    let fType = M.lookup funname $ funEnv s
    case fType of
        Nothing -> throwError $ errorFunNotExist pos funname
        Just (FunT retType argTypes) -> do
            let len1 = length argTypes
            let len2 = length args
            if len1 /= len2 then throwError $ errorFunAppArgCount pos funname len1 len2

            let typesZip = zip (\a b -> (a, b)) argTypes args
            mapM (_compareArgType funname pos) typesZip
            return retType

typeOfExpr (EString pos _) = return $ Str pos

typeOfExpr (Neg pos expr) = do
    exprType <- typeOfExpr expr
    let expected = (Int BNFC'NoPosition)
    if exprType /= expected
        then throwError $ errorUnaryOp pos expected exprType
    return $ Int pos

typeOfExpr (Not pos expr) = do
    exprType <- typeOfExpr expr
    let expected = (Bool BNFC'NoPosition)
    if exprType /= expected
        then throwError $ errorUnaryOp pos expected exprType
    return $ Bool pos

typeOfExpr (EMul pos expr1 _ expr2) =
    typeOfBinOp (Int BNFC'NoPosition) pos expr1 expr2
typeOfExpr (EAdd pos expr1 _ expr2) =
    typeOfBinOp (Int BNFC'NoPosition) pos expr1 expr2

typeOfExpr (ERel pos expr1 _ expr2) =
    typeOfBinOp (Bool BNFC'NoPosition) pos expr1 expr2
typeOfExpr (EAnd pos expr1 expr2) =
    typeOfBinOp (Bool BNFC'NoPosition) pos expr1 expr2
typeOfExpr (EOr pos expr1 expr2) =
    typeOfBinOp (Bool BNFC'NoPosition) pos expr1 expr2


typeOfBinOp :: Type -> BNFC'Position -> Expr -> Expr -> MyMonad Type
typeOfBinOp expected pos expr1 expr2 = do
    exprType1 <- typeOfExpr expr1
    exprType2 <- typeOfExpr expr2
    if exprType1 /= expected
        then throwError $ errorBinaryOp pos expected exprType1
    if exprType2 /= expected
        then throwError $ errorBinaryOp pos expected exprType2
    return $ _overwritePosition pos expected


_overwritePosition :: BNFC'Position -> Type -> Type
_overwritePosition pos (Int _) = Int pos
_overwritePosition pos (Str _) = Str pos
_overwritePosition pos (Bool _) = Bool pos
_overwritePosition pos (Tuple _ ts) = Tuple pos ts
_overwritePosition pos (Polimorph _) = Polimorph pos
_overwritePosition pos (Void _) = Void pos

_compareArgType :: Ident -> BNFC'Position -> (Type, Type) -> MyMonad Type
_compareArgType funname pos (expected, real) =
    if expected == real
        then return real
        else throwError $ errorFunAppArgType pos funname expected real

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
    let prevVar = M.lookup varname $ varEnv s
    let action = put $ _appendVar varname (VarT vartype isReadOnly) s in
        case prevVar of
            Nothing -> action >> return vartype
            Just prevType ->
                if varIsReadonly prevType
                    then throwError $
                        errorROVarOverride
                            varname
                            (varTypeOf prevType)
                            varType
                    else action >> return vartype

_changeVar :: Ident -> Type -> MyMonad Type
_changeVar varname eType env =
    s <- get
    let prevVar = M.lookup varname $ varEnv s
    case prevVar of
        Nothing -> throwError $ errorVarNotExist (hasPosition eType) varname
        Just prevType ->
            if varIsReadonly prevType
                then throwError $
                    errorROVarAssignment
                        varname
                        (varTypeOf prevType)
                        eType
                else (put $ _writeVar varname eType s) >> return eType

_appendFunction :: Ident -> FunType -> TypeEnv -> TypeEnv
_appendFunction fname ftype env =
    TypeEnv {
        funEnv = M.insert fname ftype $ funEnv env,
        varEnv = varEnv env,
        insideLoop = insideLoop env,
        insideFun = insideFun env }

_appendVar :: Ident -> VarType -> TypeEnv -> TypeEnv
_appendVar varname vartype env =
    TypeEnv {
        funEnv = funEnv env,
        varEnv = M.insert varname vartype $ varEnv env,
        insideLoop = insideLoop env,
        insideFun = insideFun env }

_appendInLoop :: Ident -> Data.Bool -> TypeEnv -> TypeEnv
_appendInLoop inLoop env =
    TypeEnv {
        funEnv = funEnv env,
        varEnv = varEnv env,
        insideLoop = inLoop,
        insideFun = insideFun env }

_appendInFun :: Ident -> Data.Bool -> TypeEnv -> TypeEnv
_appendInFun inFun env =
    TypeEnv {
        funEnv = funEnv env,
        varEnv = varEnv env,
        insideLoop = insideLoop env,
        insideFun = inFun }

_writeVar :: Ident -> Type -> TypeEnv -> TypeEnv
_writeVar varname vtype env =
    TypeEnv {
        funEnv = funEnv env,
        varEnv = M.insert varname (VarT vtype False) $ varEnv env,
        insideLoop = insideLoop env }
