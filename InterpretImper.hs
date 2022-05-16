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
        Right output -> putStrLn $ output ""
        Left er -> putStr "Error:\t" >> putStrLn er

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
    deriving (C.Eq, C.Ord, C.Show, C.Read)

type Store = M.Map Loc Val
type VarEnv = M.Map Ident Loc
type FunEnv = M.Map Ident FunData
data Global = Global {
        funEnv :: FunEnv,
        varEnv :: VarEnv,
        store :: Store,
        nextFreeLoc :: Int
    }

data FunData = FunData {
        funEnv :: FunEnv,
        varEnv :: VarEnv,
        funArgs :: [Arg],
        funBlock :: Block
    }

emptyGlobal = Global {
    funEnv = M.empty,
    varEnv = M.empty,
    store = M.empty,
    nextFreeLoc = 0
}

type MainMonad = ExceptT String (State Global)

data Interruption = None | Break | Continue | Return Val

setInterruption :: Interruption -> MainMonad ShowS -> MainMonad (ShowS, Interruption)
setInterruption inter m = do
    s <- m
    return (s, inter)

evalProgram :: Program -> Either String ShowS
evalProgram = execMainMonad.execProgram

execMainMonad :: MainMonad ShowS -> Either String ShowS
execMainMonad m = evalState (runExceptT m) emptyGlobal

execProgram :: Program -> MainMonad ShowS
execProgram (Prog _ pstmts) = execPstmts pstmts id

execPstmts :: [ProgStmt] -> ShowS -> MainMonad ShowS
execPstmts (p:ps) t =
    execPstmt p >>= execTypePstmts ps >>= (return $ t.)
execPstmts [] t = return t

execPstmt :: ProgStmt -> MainMonad ShowS
execPstmt (ProgSt _ stmt) = do
    (side, _) <- execStmt stmt
    return side
execPstmt (FnDef _ _ fname args block) =
    get >>= put $ _appendFunction fname args block >> return id

execStmt :: Stmt -> MainMonad (ShowS, Interruption)
execStmt (Decl _ assSt) = setInterruption None $ execVarDecl assSt
execStmt (DeclRO _ assSt) = setInterruption None $ execVarDecl assSt
execStmt (AssStmt _ assSt) = setInterruption None $ execAss assSt

execStmt (TupleAss p tbox expr) =
    setInterruption None $ do
        (side, val) <- execExpr expr
        reassignTElem (TupleTup p tbox) val
        return side

execStmt (Cond p ifBlock elifBlocks) =
    execStmt
        (CondElse p ifBlock elifBlocks
            (ElseBlock p
                (StBlock p [Skip p])))

execStmt (CondElse _ ifBlock elifBlocks elseBlock) = do
    (side1, success1, inter1) <- execIfBlock ifBlock
    if success1 then return (side1, inter1)
    else do
        (side2, success2, inter2) <- execElifBlocks elifBlocks id
        if success2 then return $ (side1.side2, inter2)
        else do
            (side3, _, inter3) <- execElseBlock elseBlock
            return $ (side1.side2.side3, inter3)

execStmt (For _ roAss@(Ass p iname beginE) endE block) = do
    g <- get
    (side1, _) <- execVarDecl roAss
    (_, beginVal) <- execExpr (EVar p iname)
    (side2, endVal) <- execExpr endE

    (side3, inter) <- execFor (valToInt beginVal) (valToInt endVal) block id
    
    softOverwriteEnv g
    return (side1.side2.side3, inter)

execStmt (While _ expr block) = execWhile expr block id

execStmt (Ret _ expr) = do
    (side, val) <- execExpr expr
    return (side, Return val)

execStmt (Break _) = return (id, Break)
execStmt (Continue _) = return (id, Continue)

execStmt (Print _ expr) = do
    (side, val) <- execExpr expr
    return (side.(prettyPrintVal val), None)

execStmt (Skip _) = return (id, None)

execStmt (SExp _ expr) = do
    (side, _) <- execExpr expr
    return (side, None)

execExpr :: Expr -> MainMonad (ShowS, Val)
execExpr (EVar _ name) = do
    g <- get
    let val =
        fromJust $
            M.lookup (fromJust (
                M.lookup name $ varEnv g)
            ) $ store g
    return (id, val)

execExpr (ELitInt _ i) = return (id, IntV i)
execExpr (ELitTrue _) = return (id, BoolV True)
execExpr (ELitFalse _) = return (id, BoolV False)

execExpr (ELitTuple _ exprs) =
    results <- execExprs exprs
    (sides, vals) <- unzip results
    return (foldr (.) id sides, TupleV vals)

execExpr (EApp pos fname exprs) = do
    args <- execExprs exprs
    (sides, vals) <- unzip results
    let side1 = foldr (.) id sides

    g <- get
    let f = fromJust $ M.lookup fname $ funEnv g
    put $ Global {
        funEnv = funEnv f,
        varEnv = varEnv f,
        store = store g,
        nextFreeLoc = nextFreeLoc g
    }

    addFunArgs $ zip (funArgs f) vals
    (side2, inter) <- execBlock (funBlock f)

    case inter of
        Return r -> do
            softOverwriteEnv g
            return (side1.side2, r)
        _ -> throwError $ errorFunNoReturn pos fname

execExpr (EString _ s) = return (id, StrV s)

execExpr (Neg _ expr) =
    (side, val) <- execExpr expr
    let num = valToInt val
    return (side, IntV $ -num)

execExpr (Not _ expr) =
    (side, val) <- execExpr expr
    let b = valToBool val
    return (side, BoolV $ not b)

execExpr (EMul p e1 op e2) =
    execMul p op e1 e2

execExpr (EAdd _ e1 op e2) = do
    (side1, v1) <- execExpr e1
    (side2, v2) <- execExpr e2
    let val1 = valToInt v1
    let val2 = valToInt v2
    return (side1.side2, IntV $ funOp op val1 val2)

execExpr (ERel _ e1 op e2) = do
    (side1, v1) <- execExpr e1
    (side2, v2) <- execExpr e2
    let val1 = valToInt v1
    let val2 = valToInt v2
    return (side1.side2, BoolV $ funOp op val1 val2)

execExpr (EAnd _ e1 e2) =
    execBinBoolOp (&&) e1 e2

execExpr (EOr _ e1 e2) =
    execBinBoolOp (||) e1 e2

execExprs :: [Expr] -> MainMonad [(ShowS, Val)]
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
    let nfl = nextFreeLoc g
    put $ _writeStore nfl val
        $ _addVar varname nfl
        $ _incrementNextFreeLoc g

addFunArgs :: [(Arg, Val)] -> MainMonad ()
addFunArgs zipped =
    mapM_ addFunArg zipped

addFunArg :: (Arg, Val) -> MainMonad ()
addFunArg ((FnArg _ _ argname), argval) =
    addVar argname argval

execVarDecl :: AStmt -> MainMonad ShowS
execVarDecl (Ass _ varname expr) = do
    (side, val) <- execExpr expr
    addVar varname val
    return side

execAss :: AStmt -> MainMonad ShowS
execAss (Ass _ varname expr) = do
    (side, val) <- execExpr expr
    changeVar varname val
    return side

execIfBlock :: IfBl -> MainMonad (ShowS, Bool, Interruption)
execIfBlock (IfBlock _ expr block) =
    execCond expr block

execElifBlocks :: [ElifBl] -> ShowS -> MainMonad (ShowS, Bool, Interruption)
execElifBlocks (e:es) acc = do
    (side, success, inter) <- execElifBlock e
    if success
        then return (acc.side, True, inter)
        else execElifBlocks es $ acc.side
execElifBlocks [] acc = return (acc, False, None)

execElifBlock :: ElifBl -> MainMonad (ShowS, Bool, Interruption)
execElifBlock (ElifBlock _ expr block) =
    execCond expr block

execElseBlock :: ElseBl -> MainMonad (ShowS, Bool, Interruption)
execElseBlock (ElseBlock p block) =
    execCond (ELitTrue p) block

execCond :: Expr -> Block -> MainMonad (ShowS, Bool, Interruption)
execCond expr block = do
    (side, val) <- execExpr expr
    case val of
        BoolV b ->
            if b
                then do
                    (sideBlock, inter) <- execBlock block
                    return (side.sideBlock, True, inter)
                else
                    return (side, False, None)
        _ -> undefined

execBlock :: Block -> MainMonad (ShowS, Interruption)
execBlock (StBlock _ stmts) = do
    g <- get
    side <- execStmts stmts id
    softOverwriteEnv g
    return side

execStmts :: [Stmt] -> ShowS -> MainMonad (ShowS, Interruption)
execStmts (s:st) acc = do
    (side, inter) <- execStmt s
    case inter of
        None -> execStmts st (acc.side)
        _ -> return (acc.side, inter)
execStmts [] acc = return (acc, None)

execFor :: Int -> Int -> Block -> ShowS -> MainMonad (ShowS, Interruption)
execFor begin end block acc =
    let nextIter = if begin <= end then (1+) else (1-)
    in do
        (side, inter) <- execBlock block
        case inter of
            Break -> return (acc.side, None)
            Return _ -> return (acc.side, inter)
            _ ->
                if begin == end
                    then return (acc.side, None)
                    else execFor (nextIter begin) end block $ acc.side

execWhile :: Expr -> Block -> ShowS -> MainMonad (ShowS, Interruption)
execWhile expr block acc = do
    (side1, val) <- execExpr expr
    if valToBool val
        then do
            (side2, inter) <- execBlock block
            case inter of
                Break -> return (acc.side1.side2, None)
                Return _ -> return (acc.side1.side2, inter)
                _ -> execWhile expr block $ acc.side1.side2
        else return (acc.side1, None)

execMul :: BNFC'Position -> MulOp -> Expr -> Expr -> MainMonad (ShowS, Val)
execMul _ op@(Times _) e1 e2 = do
    (side1, v1) <- execExpr e1
    (side2, v2) <- execExpr e2
    let val1 = valToInt v1
    let val2 = valToInt v2

    return (side1.side2, IntV $ funOp op val1 val2)

execMul p op@(Div _) e1 e2 = do
    (side1, v1) <- execExpr e1
    (side2, v2) <- execExpr e2
    let val1 = valToInt v1
    let val2 = valToInt v2
    
    if val2 == 0
        then throwError $ errorDivZero p val1
        else return (side1.side2, IntV $ funOp op val1 val2)

execMul p op@(Mod _) e1 e2 = do
    (side1, v1) <- execExpr e1
    (side2, v2) <- execExpr e2
    let val1 = valToInt v1
    let val2 = valToInt v2
    
    if val2 == 0
        then throwError $ errorModZero p val1
        else return (side1.side2, IntV $ funOp op val1 val2)

execBinBoolOp :: (Bool -> Bool -> Bool) -> Expr -> Expr -> MainMonad (ShowS, Val)
execBinBoolOp binOp e1 e2 = do
    (side1, v1) <- execExpr e1
    (side2, v2) <- execExpr e2
    let val1 = valToBool v1
    let val2 = valToBool v2
    return (side1.side2, BoolV $ binOp val1 val2)

funOp :: MulOp -> (Int -> Int -> Int)
funOp (Times _) = (*)
funOp (Div _) = div
funOp (Mod _) = mod

funOp :: AddOp -> (Int -> Int -> Int)
funOp (Plus _) = (+)
funOp (Minus _) = (-)

funOp :: RelOp -> (Int -> Int -> Bool)
funOp (LTH _) = (<)
funOp (LE _) = (<=)
funOp (GTH _) = (>)
funOp (GE _) = (>=)
funOp (EQU _) = (==)
funOp (NE _) = (!=)

softOverwriteEnv :: Global -> MainMonad ()
softOverwriteEnv g = do
    g' <- get
    let funenv = funEnv g
    let varenv = varEnv g
    let sstore = store g'
    let nextfreeloc = nextFreeLoc g
    put $ Global funenv varenv sstore nextfreeloc

_appendFunction :: Ident -> [Arg] -> Block -> Global -> Global
_appendFunction fname args funblock glob =
    Global {
        funEnv =
            _appendFunctionRecursive fname args funblock glob,
        varEnv = varEnv glob,
        store = store glob,
        nextFreeLoc = nextFreeLoc glob }

_appendVar :: Ident -> Loc -> Global -> Global
_appendVar varname loc glob =
    Global {
        funEnv = funEnv glob,
        varEnv = M.insert varname loc $ varEnv glob,
        store = store glob,
        nextFreeLoc = nextFreeLoc glob }

_appendFunctionRecursive :: Ident -> [Arg] -> Block -> Global -> FunEnv
_appendFunctionRecursive fname args funblock glob =
    M.insert
        fname,
        FunData {
            funEnv =
                _appendFunctionRecursive fname args funblock glob,
            varEnv = varEnv glob,
            funArgs = args,
            funBlock = funblock
        } $ funEnv glob

_incrementNextFreeLoc :: Global -> Global
_incrementNextFreeLoc glob =
    Global {
        funEnv = funEnv glob,
        varEnv = varEnv glob,
        store = store glob,
        nextFreeLoc = 1 + nextFreeLoc glob }

_writeStore :: Loc -> Val -> Global -> Global
_writeStore loc val glob =
    Global {
        funEnv = funEnv glob,
        varEnv = varEnv glob,
        store = M.insert loc val $ store glob,
        nextFreeLoc = nextFreeLoc glob }