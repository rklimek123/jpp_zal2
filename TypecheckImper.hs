module TypecheckImper (typeCheck)
where

import qualified Data.Map as M

import Control.Monad.Except
import Control.Monad.State

import System.IO (hPutStrLn, stdin, stderr)

import AbsImper
import ErrorImper
import InterpretImper (interpret)

typeCheck :: Program -> IO()
typeCheck p =
    case evalProgram p of
        Right _ -> interpret p
        Left er -> putStr "Error:\t" >> putStrLn er

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

type VarTypeEnv = M.Map Ident VarType
type FunTypeEnv = M.Map Ident FunType
data TypeEnv = TypeEnv {
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

type TypeMonad = ExceptT String (State TypeEnv)

evalProgram :: Program -> Either String ()
evalProgram = execTypeMonad.execTypeProgram

execTypeMonad :: TypeMonad () -> Either String ()
execTypeMonad m = evalState (runExceptT m) emptyTypeEnv

execTypeProgram :: Program -> TypeMonad ()
execTypeProgram (Prog _ pstmts) = execTypePstmts pstmts

execTypePstmts :: [ProgStmt] -> TypeMonad ()
execTypePstmts (p:ps) = execTypePstmt p >> execTypePstmts ps
execTypePstmts [] = return ()


execTypePstmt :: ProgStmt -> TypeMonad ()
execTypePstmt (ProgSt _ stmt) = execTypeStmt stmt
execTypePstmt (FnDef _ retType fname args block) = do
    s <- get

    _addArgs args
    s' <- get
    put $ _appendInFun True (_appendFunction fname ftype s')
    
    realRetT <- inferTypeOfBlock block retType
    
    put $ _appendFunction fname ftype s
    
    case realRetT of
        Nothing -> throwError $ errorFunType fname retType realRetT
        Just realRetType ->
            if realRetType == retType
                then return ()
                else throwError $ errorFunType fname retType realRetT
  where
      ftype = FunT retType $ _argsToTypes args


-- check if the types are correct inside the block
-- and the only type that can be returned matches the parameter Type
inferTypeOfBlock :: Block -> Type -> TypeMonad (Maybe Type)
inferTypeOfBlock (StBlock pos stmts) infType = do
    s <- get
    retType <- inferTypeReturn stmts infType Nothing
    put s
    return retType

inferTypeReturn :: [Stmt] -> Type -> Maybe Type -> TypeMonad (Maybe Type)
inferTypeReturn (s:st) infType retType =
    inferTypeReturnSingle s infType retType >>= inferTypeReturn st infType
inferTypeReturn [] _ retType = return retType

inferTypeReturnSingle :: Stmt -> Type -> Maybe Type -> TypeMonad (Maybe Type)
inferTypeReturnSingle st infType retType =
    execTypeStmt st >> inferReturnedType st infType retType

inferReturnedType :: Stmt -> Type -> Maybe Type -> TypeMonad (Maybe Type)
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

inferReturnedType st _ t = execTypeStmt st >> return t

condTrue :: Expr
condTrue = ELitTrue BNFC'NoPosition

inferReturnedTypeIf :: IfBl -> Type -> Maybe Type -> TypeMonad (Maybe Type)
inferReturnedTypeIf (IfBlock _ expr block) =
    inferReturnedTypeInBlock block

inferReturnedTypeElifs :: [ElifBl] -> Type -> Maybe Type -> TypeMonad (Maybe Type)
inferReturnedTypeElifs (e:es) infType retType =
    inferReturnedTypeElif e infType retType >>= inferReturnedTypeElifs es infType
inferReturnedTypeElifs [] _ t = return t

inferReturnedTypeElif :: ElifBl -> Type -> Maybe Type -> TypeMonad (Maybe Type)
inferReturnedTypeElif (ElifBlock _ _ block) =
    inferReturnedTypeInBlock block

inferReturnedTypeElse :: ElseBl -> Type -> Maybe Type -> TypeMonad (Maybe Type)
inferReturnedTypeElse (ElseBlock _ block) =
    inferReturnedTypeInBlock block

inferReturnedTypeInBlock :: Block -> Type -> Maybe Type -> TypeMonad (Maybe Type)
inferReturnedTypeInBlock block infType retType = do
    blockType <- inferTypeOfBlock block infType
    case blockType of
        Nothing -> return retType
        _ -> return blockType

execTypeStmts :: [Stmt] -> TypeMonad ()
execTypeStmts (st:sts) = execTypeStmt st >> execTypeStmts sts
execTypeStmts [] = return ()

execTypeStmt :: Stmt -> TypeMonad ()
execTypeStmt (Decl _ assSt) =
    execTypeVarDecl False assSt >> return ()

execTypeStmt (DeclRO _ assSt) =
    execTypeVarDecl True assSt >> return ()

execTypeStmt (AssStmt _ assSt) = execTypeAss assSt

execTypeStmt (TupleAss _ tbox expr) = do
    exprType <- typeOfExpr expr
    tboxType <- typeOfTBox tbox
    if exprType == tboxType
        then return ()
        else throwError $ errorTupleType tboxType exprType

execTypeStmt (Cond _ ifBlock elifBlocks) =
    execTypeIf ifBlock >> execTypeElifs elifBlocks

execTypeStmt (CondElse _ ifBlock elifBlocks elseBlock) =
    execTypeIf ifBlock >> execTypeElifs elifBlocks >> execTypeElse elseBlock

execTypeStmt (For _ roAss expr block) = do
    s <- get
    
    endType <- typeOfExpr expr
    if endType /= (Int BNFC'NoPosition)
        then throwError $ errorForIterType endType
        else pure ()
    
    beginType <- execTypeVarDecl True roAss
    if beginType /= (Int BNFC'NoPosition)
        then throwError $ errorForIterType beginType
        else pure ()

    s' <- get
    put $ _appendInLoop True s'

    execTypeBlock block
    put s

execTypeStmt (While _ expr block) = do
    s <- get
    put $ _appendInLoop True s
    execTypeCondBlock expr block
    put s

execTypeStmt (Ret pos expr) = do
    s <- get

    if not $ insideFun s
        then throwError $ errorRetOutsideFun pos
        else typeOfExpr expr >> return ()

execTypeStmt (Break pos) = execTypeJump True pos
execTypeStmt (Continue pos) = execTypeJump False pos

execTypeStmt (Print _ expr) =
    typeOfExpr expr >> return ()

execTypeStmt (Skip _) = return ()

execTypeStmt (SExp _ expr) =
    typeOfExpr expr >> return ()

execTypeVarDecl :: Bool -> AStmt -> TypeMonad Type
execTypeVarDecl isReadOnly (Ass _ varname expr) = do
    exprType <- typeOfExpr expr
    _addVar varname exprType isReadOnly
    return exprType

execTypeAss :: AStmt -> TypeMonad ()
execTypeAss (Ass _ varname expr) = do
    exprType <- typeOfExpr expr
    _changeVar varname exprType

typeOfTBox :: TBox -> TypeMonad Type
typeOfTBox (TupleBox pos tElems) = do
    types <- typeOfTElems tElems
    return (Tuple pos types)

typeOfTElems :: [TElem] -> TypeMonad [Type]
typeOfTElems = mapM typeOfTElem

typeOfTElem :: TElem -> TypeMonad Type
typeOfTElem (TupleTup _ tbox) =
    typeOfTBox tbox

typeOfTElem (TupleAtom pos varname) = do
    s <- get
    let mVartype = M.lookup varname $ varEnv s
    case mVartype of
        Nothing -> throwError $ errorVarNotExist pos varname
        Just vartype -> return (varTypeOf vartype)

typeOfTElem (TupleIgn pos) =
    return (Polimorph pos)

execTypeIf :: IfBl -> TypeMonad ()
execTypeIf (IfBlock _ expr block) = execTypeCondBlock expr block

execTypeElifs :: [ElifBl] -> TypeMonad ()
execTypeElifs (e:es) =
    execTypeElif e >> execTypeElifs es
execTypeElifs [] = return ()

execTypeElif :: ElifBl -> TypeMonad ()
execTypeElif (ElifBlock _ expr block) = execTypeCondBlock expr block

execTypeElse :: ElseBl -> TypeMonad ()
execTypeElse (ElseBlock _ block) = execTypeCondBlock condTrue block

execTypeCondBlock :: Expr -> Block -> TypeMonad ()
execTypeCondBlock expr block = do
    exprType <- typeOfExpr expr
    if exprType /= (Bool BNFC'NoPosition)
        then throwError $ errorCondExprType exprType
        else execTypeBlock block >> return ()

execTypeJump :: Bool -> BNFC'Position -> TypeMonad ()
execTypeJump isBreak pos = do
    s <- get

    if not $ insideLoop s
        then throwError $ errorJumpOutsideLoop isBreak pos
        else return ()

execTypeBlock :: Block -> TypeMonad ()
execTypeBlock (StBlock _ stmts) = do
    s <- get
    retType <- execTypeStmts stmts
    put s

typeOfExpr :: Expr -> TypeMonad Type
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
            if len1 /= len2
                then throwError $ errorFunAppArgCount pos funname len1 len2
                else pure ()

            givenArgsTypes <- mapM typeOfExpr args
            let typesZip = zip argTypes givenArgsTypes
            mapM (_compareArgType funname pos) typesZip
            return retType

typeOfExpr (EString pos _) = return $ Str pos

typeOfExpr (Neg pos expr) = do
    exprType <- typeOfExpr expr
    let expected = (Int BNFC'NoPosition)
    if exprType /= expected
        then throwError $ errorUnaryOp pos expected exprType
        else pure ()

    return $ Int pos

typeOfExpr (Not pos expr) = do
    exprType <- typeOfExpr expr
    let expected = (Bool BNFC'NoPosition)
    if exprType /= expected
        then throwError $ errorUnaryOp pos expected exprType
        else pure ()

    return $ Bool pos

typeOfExpr (EMul pos expr1 _ expr2) =
    typeOfBinOp (Int BNFC'NoPosition) pos expr1 expr2 (Int BNFC'NoPosition)
typeOfExpr (EAdd pos expr1 _ expr2) =
    typeOfBinOp (Int BNFC'NoPosition) pos expr1 expr2 (Int BNFC'NoPosition)

typeOfExpr (ERel pos expr1 _ expr2) =
    typeOfBinOp (Int BNFC'NoPosition) pos expr1 expr2 (Bool BNFC'NoPosition)
typeOfExpr (EAnd pos expr1 expr2) =
    typeOfBinOp (Bool BNFC'NoPosition) pos expr1 expr2 (Bool BNFC'NoPosition)
typeOfExpr (EOr pos expr1 expr2) =
    typeOfBinOp (Bool BNFC'NoPosition) pos expr1 expr2 (Bool BNFC'NoPosition)


typeOfBinOp :: Type -> BNFC'Position -> Expr -> Expr -> Type -> TypeMonad Type
typeOfBinOp expected pos expr1 expr2 expectRet = do
    exprType1 <- typeOfExpr expr1
    exprType2 <- typeOfExpr expr2
    if exprType1 /= expected
        then throwError $ errorBinaryOp pos expected exprType1
        else pure ()
    if exprType2 /= expected
        then throwError $ errorBinaryOp pos expected exprType2
        else pure ()
    return $ _overwritePosition pos expectRet


_overwritePosition :: BNFC'Position -> Type -> Type
_overwritePosition pos (Int _) = Int pos
_overwritePosition pos (Str _) = Str pos
_overwritePosition pos (Bool _) = Bool pos
_overwritePosition pos (Tuple _ ts) = Tuple pos ts
_overwritePosition pos (Polimorph _) = Polimorph pos

_compareArgType :: Ident -> BNFC'Position -> (Type, Type) -> TypeMonad ()
_compareArgType funname pos (expected, real) =
    if expected == real
        then return ()
        else throwError $ errorFunAppArgType pos funname expected real

_argsToTypes :: [Arg] -> [Type]
_argsToTypes = map _argToType

_argToType :: Arg -> Type
_argToType (FnArg _ t _) = t

_addArgs :: [Arg] -> TypeMonad ()
_addArgs (a:as) = (_addArg a) >> (_addArgs as)
_addArgs [] = return ()

_addArg :: Arg -> TypeMonad ()
_addArg (FnArg _ t argname) = _addVar argname t False

-- read-only variables cannot be overriden
_addVar :: Ident -> Type -> Bool -> TypeMonad ()
_addVar varname vartype isReadOnly = do
    s <- get
    let prevVar = M.lookup varname $ varEnv s
    let action = put $ _appendVar varname (VarT vartype isReadOnly) s in
        case prevVar of
            Nothing -> action
            Just prevType ->
                if varIsReadonly prevType
                    then throwError $
                        errorROVarOverride
                            varname
                            (varTypeOf prevType)
                            vartype
                    else action

_changeVar :: Ident -> Type -> TypeMonad ()
_changeVar varname eType = do
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
                else put $ _writeVar varname eType s

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

_appendInLoop :: Bool -> TypeEnv -> TypeEnv
_appendInLoop inLoop env =
    TypeEnv {
        funEnv = funEnv env,
        varEnv = varEnv env,
        insideLoop = inLoop,
        insideFun = insideFun env }

_appendInFun :: Bool -> TypeEnv -> TypeEnv
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
        insideLoop = insideLoop env,
        insideFun = insideFun env }
