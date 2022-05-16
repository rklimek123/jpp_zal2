module InterpretImper
where

import qualified Data.Map as M
import Data.Maybe

import Control.Monad.Except
import Control.Monad.State

import AbsImper
import ErrorImper

interpret :: Program -> IO()
interpret p =
    case evalProgram p of
        Right output -> output
        Left er -> putStrLn er

data Val = IntV Int | BoolV Bool | StrV String | TupleV [Val]
valToInt :: Val -> Int
valToInt (IntV a) = a
valToInt _ = undefined

valToBool :: Val -> Bool
valToBool (BoolV a) = a
valToBool _ = undefined

prettyPrintVal :: Val -> ShowS
prettyPrintVal (IntV a) = shows a
prettyPrintVal (BoolV a) = shows a
prettyPrintVal (StrV a) = showString a
prettyPrintVal (TupleV vals) =
    (showString "<< ").
    (prettyPrintVals False vals).
    (showString " >>")

prettyPrintVals :: Bool -> [Val] -> ShowS
prettyPrintVals showComma (v:vs) =
    (if showComma then showString ", " else id).
    (prettyPrintVal v).
    (prettyPrintVals True vs)
prettyPrintVals _ [] = id

newtype Loc = Loc Int
    deriving (Eq, Ord, Show, Read)

type Store = M.Map Loc Val
type VarEnv = M.Map Ident Loc
type FunEnv = M.Map Ident FunData
data Global = Global {
        funEnv :: FunEnv,
        varEnv :: VarEnv,
        store :: Store,
        nextFreeLoc :: Int,
        stdOut :: ShowS
    }

data FunData = FunData {
        funEnvF :: FunEnv,
        varEnvF :: VarEnv,
        funArgs :: [Arg],
        funBlock :: Block
    }

emptyGlobal = Global {
    funEnv = M.empty,
    varEnv = M.empty,
    store = M.empty,
    nextFreeLoc = 0,
    stdOut = id
}

data Interruption = INone | IBreak | IContinue | IReturn Val

type MainMonad = ExceptT String (State Global)

evalProgram :: Program -> Either String (IO())
evalProgram = execMainMonad.execProgram

execMainMonad :: MainMonad (IO()) -> Either String (IO())
execMainMonad m = evalState (runExceptT m) emptyGlobal

execProgram :: Program -> MainMonad (IO())
execProgram (Prog _ pstmts) = do
    execPstmts pstmts
    g <- get
    return $ putStrLn (stdOut g "")

execPstmts :: [ProgStmt] -> MainMonad ()
execPstmts (p:ps) =
    execPstmt p >> execPstmts ps
execPstmts [] = return ()

execPstmt :: ProgStmt -> MainMonad ()
execPstmt (ProgSt _ stmt) = execStmt stmt >> return ()
execPstmt (FnDef _ _ fname args block) = do
    g <- get
    put $ _appendFunction fname args block g

execStmt :: Stmt -> MainMonad Interruption
execStmt (Decl _ assSt) = execVarDecl assSt >> return INone
execStmt (DeclRO _ assSt) = execVarDecl assSt >> return INone
execStmt (AssStmt _ assSt) = execAss assSt >> return INone

execStmt (TupleAss p tbox expr) =
    execExpr expr >>= reassignTElem (TupleTup p tbox) >> return INone

execStmt (Cond p ifBlock elifBlocks) =
    execStmt
        (CondElse p ifBlock elifBlocks
            (ElseBlock p
                (StBlock p [Skip p])))

execStmt (CondElse _ ifBlock elifBlocks elseBlock) = do
    (success1, inter1) <- execIfBlock ifBlock
    if success1 then return inter1
    else do
        (success2, inter2) <- execElifBlocks elifBlocks
        if success2 then return inter2
        else do
            (_, inter3) <- execElseBlock elseBlock
            return inter3

execStmt (For _ roAss@(Ass p iname beginE) endE block) = do
    g <- get
    execVarDecl roAss
    beginVal <- execExpr (EVar p iname)
    endVal <- execExpr endE

    inter <- execFor (valToInt beginVal) (valToInt endVal) block
    
    softOverwriteEnv g
    return inter

execStmt (While _ expr block) = execWhile expr block

execStmt (Ret _ expr) = do
    val <- execExpr expr
    return $ IReturn val

execStmt (Break _) = return IBreak
execStmt (Continue _) = return IContinue

execStmt (Print _ expr) = do
    val <- execExpr expr
    g <- get
    let toOut = prettyPrintVal val
    put $ _writeToStdOut toOut g

    return INone

execStmt (Skip _) = return INone

execStmt (SExp _ expr) =
    execExpr expr >> return INone

execExpr :: Expr -> MainMonad Val
execExpr (EVar _ name) = do
    g <- get
    let val = fromJust (M.lookup (fromJust (M.lookup name $ varEnv g)) $ store g)
    return val

execExpr (ELitInt _ i) = return $ IntV (fromInteger i)
execExpr (ELitTrue _) = return $ BoolV True
execExpr (ELitFalse _) = return $ BoolV False

execExpr (ELitTuple _ exprs) = do
    vals <- execExprs exprs
    return $ TupleV vals

execExpr (EApp pos fname exprs) = do
    argVals <- execExprs exprs

    g <- get
    let f = fromJust $ M.lookup fname $ funEnv g
    put $ Global {
        funEnv = funEnvF f,
        varEnv = varEnvF f,
        store = store g,
        nextFreeLoc = nextFreeLoc g,
        stdOut = stdOut g
    }

    addFunArgs $ zip (funArgs f) argVals
    inter <- execBlock $ funBlock f

    case inter of
        IReturn r -> do
            softOverwriteEnv g
            return r
        _ -> do
            g' <- get
            throwError $ errorFunNoReturn (stdOut g') pos fname

execExpr (EString _ s) = return $ StrV s

execExpr (Neg _ expr) = do
    val <- execExpr expr
    let num = valToInt val
    return $ IntV (-num)

execExpr (Not _ expr) = do
    val <- execExpr expr
    let b = valToBool val
    return $ BoolV (not b)

execExpr (EMul p e1 op e2) =
    execMul p op e1 e2

execExpr (EAdd _ e1 op e2) = do
    v1 <- execExpr e1
    v2 <- execExpr e2
    let val1 = valToInt v1
    let val2 = valToInt v2
    return $ IntV (funOpAdd op val1 val2)

execExpr (ERel _ e1 op e2) = do
    v1 <- execExpr e1
    v2 <- execExpr e2
    let val1 = valToInt v1
    let val2 = valToInt v2
    return $ BoolV (funOpRel op val1 val2)

execExpr (EAnd _ e1 e2) =
    execBinBoolOp (&&) e1 e2

execExpr (EOr _ e1 e2) =
    execBinBoolOp (||) e1 e2

execExprs :: [Expr] -> MainMonad [Val]
execExprs = mapM execExpr

reassignTElems :: [TElem] -> [Val] -> MainMonad ()
reassignTElems (t:ts) (v:vs) =
    reassignTElem t v >> reassignTElems ts vs
reassignTElems [] [] = return ()
reassignTElems _ _ = undefined

reassignTElem :: TElem -> Val -> MainMonad ()
reassignTElem (TupleTup _ (TupleBox _ tElems)) (TupleV tVals) =
    reassignTElems tElems tVals

reassignTElem (TupleAtom _ varname) val =
    changeVar varname val

reassignTElem (TupleIgn _) _ = return ()
reassignTElem _ _ = undefined

changeVar :: Ident -> Val -> MainMonad ()
changeVar varname val = do
    g <- get
    let locInStore = fromJust $ M.lookup varname $ varEnv g
    put $ _writeStore locInStore val g

addVar :: Ident -> Val -> MainMonad ()
addVar varname val = do
    g <- get
    let nfl = Loc $ nextFreeLoc g
    put $ _writeStore nfl val
        $ _appendVar varname nfl
        $ _incrementNextFreeLoc g

addFunArgs :: [(Arg, Val)] -> MainMonad ()
addFunArgs zipped =
    mapM_ addFunArg zipped

addFunArg :: (Arg, Val) -> MainMonad ()
addFunArg ((FnArg _ _ argname), argval) =
    addVar argname argval

execVarDecl :: AStmt -> MainMonad ()
execVarDecl (Ass _ varname expr) =
    execExpr expr >>= addVar varname

execAss :: AStmt -> MainMonad ()
execAss (Ass _ varname expr) = do
    execExpr expr >>= changeVar varname

execIfBlock :: IfBl -> MainMonad (Bool, Interruption)
execIfBlock (IfBlock _ expr block) =
    execCond expr block

execElifBlocks :: [ElifBl] -> MainMonad (Bool, Interruption)
execElifBlocks (e:es) = do
    (success, inter) <- execElifBlock e
    if success
        then return (True, inter)
        else execElifBlocks es
execElifBlocks [] = return (False, INone)

execElifBlock :: ElifBl -> MainMonad (Bool, Interruption)
execElifBlock (ElifBlock _ expr block) =
    execCond expr block

execElseBlock :: ElseBl -> MainMonad (Bool, Interruption)
execElseBlock (ElseBlock p block) =
    execCond (ELitTrue p) block

execCond :: Expr -> Block -> MainMonad (Bool, Interruption)
execCond expr block = do
    val <- execExpr expr
    case val of
        BoolV b ->
            if b
                then do
                    inter <- execBlock block
                    return (True, inter)
                else
                    return (False, INone)
        _ -> undefined

execBlock :: Block -> MainMonad Interruption
execBlock (StBlock _ stmts) = do
    g <- get
    inter <- execStmts stmts
    softOverwriteEnv g
    return inter

execStmts :: [Stmt] -> MainMonad Interruption
execStmts (s:st) = do
    inter <- execStmt s
    case inter of
        INone -> execStmts st
        _ -> return inter
execStmts [] = return INone

execFor :: Int -> Int -> Block -> MainMonad Interruption
execFor begin end block =
    let nextIter = if begin <= end then (1+) else (1-)
    in do
        inter <- execBlock block
        case inter of
            IBreak -> return INone
            IReturn _ -> return inter
            _ ->
                if begin == end
                    then return INone
                    else execFor (nextIter begin) end block

execWhile :: Expr -> Block -> MainMonad Interruption
execWhile expr block = do
    val <- execExpr expr
    if valToBool val
        then do
            inter <- execBlock block
            case inter of
                IBreak -> return INone
                IReturn _ -> return inter
                _ -> execWhile expr block
        else return INone

execMul :: BNFC'Position -> MulOp -> Expr -> Expr -> MainMonad Val
execMul _ op@(Times _) e1 e2 = do
    v1 <- execExpr e1
    v2 <- execExpr e2
    let val1 = valToInt v1
    let val2 = valToInt v2

    return $ IntV (funOpMul op val1 val2)

execMul p op@(Div _) e1 e2 = do
    v1 <- execExpr e1
    v2 <- execExpr e2
    let val1 = valToInt v1
    let val2 = valToInt v2
    g <- get

    if val2 == 0
        then throwError $ errorDivZero (stdOut g) p val1
        else return $ IntV (funOpMul op val1 val2)

execMul p op@(Mod _) e1 e2 = do
    v1 <- execExpr e1
    v2 <- execExpr e2
    let val1 = valToInt v1
    let val2 = valToInt v2
    g <- get
    
    if val2 == 0
        then throwError $ errorModZero (stdOut g) p val1
        else return $ IntV (funOpMul op val1 val2)

execBinBoolOp :: (Bool -> Bool -> Bool) -> Expr -> Expr -> MainMonad Val
execBinBoolOp binOp e1 e2 = do
    v1 <- execExpr e1
    v2 <- execExpr e2
    let val1 = valToBool v1
    let val2 = valToBool v2
    return $ BoolV (binOp val1 val2)

funOpMul :: MulOp -> (Int -> Int -> Int)
funOpMul (Times _) = (*)
funOpMul (Div _) = div
funOpMul (Mod _) = mod

funOpAdd :: AddOp -> (Int -> Int -> Int)
funOpAdd (Plus _) = (+)
funOpAdd (Minus _) = (-)

funOpRel :: RelOp -> (Int -> Int -> Bool)
funOpRel (LTH _) = (<)
funOpRel (LE _) = (<=)
funOpRel (GTH _) = (>)
funOpRel (GE _) = (>=)
funOpRel (EQU _) = (==)
funOpRel (NE _) = (/=)

softOverwriteEnv :: Global -> MainMonad ()
softOverwriteEnv g = do
    g' <- get
    let funenv = funEnv g
    let varenv = varEnv g
    let sstore = store g'
    let nextfreeloc = nextFreeLoc g
    let stdout = stdOut g'
    put $ Global funenv varenv sstore nextfreeloc stdout

_appendFunction :: Ident -> [Arg] -> Block -> Global -> Global
_appendFunction fname args funblock glob =
    glob {
        funEnv = _appendFunctionRecursive fname args funblock glob
    }

_appendVar :: Ident -> Loc -> Global -> Global
_appendVar varname loc glob =
    glob {
        varEnv = M.insert varname loc $ varEnv glob
    }

_appendFunctionRecursive :: Ident -> [Arg] -> Block -> Global -> FunEnv
_appendFunctionRecursive fname args funblock glob =
    M.insert
        fname
        FunData {
            funEnvF =
                _appendFunctionRecursive fname args funblock glob,
            varEnvF = varEnv glob,
            funArgs = args,
            funBlock = funblock
        } $ funEnv glob

_incrementNextFreeLoc :: Global -> Global
_incrementNextFreeLoc glob =
    glob {
        nextFreeLoc = 1 + nextFreeLoc glob
    }

_writeStore :: Loc -> Val -> Global -> Global
_writeStore loc val glob =
    glob {
        store = M.insert loc val $ store glob }

_writeToStdOut :: ShowS -> Global -> Global
_writeToStdOut toWrite glob =
    glob {
        stdOut = (stdOut glob).toWrite }