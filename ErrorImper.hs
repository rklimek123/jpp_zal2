module ErrorImper
where

import AbsImper

prettyType :: Type -> ShowS
prettyType (Int _) = showString "int"
prettyType (Str _) = showString "string"
prettyType (Bool _) = showString "bool"
prettyType (Polimorph _) = showString "_"
prettyType (Tuple _ types) =
    (showString "(")
    .(prettyTypesComma False types)
    .(showString ")")

prettyTypesComma :: Bool -> [Type] -> ShowS
prettyTypesComma showComma (t:ts) =
    (if showComma
        then showString ", "
        else id).
    (prettyType t).
    (prettyTypesComma True ts)
prettyTypesComma _ [] = id

prettyTypeWithAt :: Type -> ShowS
prettyTypeWithAt t =
    (showString "|").
    (prettyType t).
    (showString "|").
    (prettyPositionAt True $ hasPosition t)

prettyPosition :: Bool -> BNFC'Position -> ShowS
prettyPosition signalNothing pos =
    case pos of
        Nothing ->
            if signalNothing
                then showString "[unknown position]"
                else id
        Just (line, col) ->
            (showString "[line ").
            (shows line).
            (showString ", col ").
            (shows col).
            (showString "]")

prettyPositionAt :: Bool -> BNFC'Position -> ShowS
prettyPositionAt putSpace pos =
    case pos of
        Nothing -> id
        Just (line, col) ->
            (if putSpace
                then showString " "
                else id).
            (showString "at ").
            (prettyPosition True pos)

prettyPositionAtShort :: BNFC'Position -> ShowS
prettyPositionAtShort pos =
    (showString "\tAt position ").
    (prettyPosition True pos)

msgShouldBeButIs :: Type -> Type -> ShowS
msgShouldBeButIs expected real =
    (prettyPositionAtShort $ hasPosition real).
    (showString " type should be ").
    (prettyType expected).
    (showString ",\n").

    (showString "\tbut actually evaluates to ").
    (prettyType real)

msgOperatorError :: BNFC'Position -> Type -> Type -> ShowS
msgOperatorError pos expected real =
    (showString "operator error").
    (prettyPositionAt True pos).
    (showString "\n").
    (msgShouldBeButIs expected real)

errorFunType :: Ident -> Type -> Maybe Type -> String
errorFunType (Ident name) expected real =
    (showString "Function `").
    (showString name).
    (showString "` returns a wrong type.\n").

    (showString "\tShould've returned ").
    (prettyTypeWithAt expected).
    (showString "\n").
    
    (showString "\t").
    (case real of
        Nothing ->
            showString "Didn't return anything"
        Just ret ->
            (showString "Returned ").
            (prettyTypeWithAt ret)) $ ""

errorFunTypeReturn :: BNFC'Position -> Type -> Type -> String
errorFunTypeReturn pos expected real =
    (showString "Returning wrong type in function.\n").
    
    (prettyPositionAtShort pos).
    (showString " returning ").
    (prettyType real).
    (showString ",\n").

    (showString "\tbut should've returned ").
    (prettyType expected) $ ""

errorTupleType :: Type -> Type -> String
errorTupleType expected real =
    (showString "Tuple assignment type error.\n").
    (msgShouldBeButIs expected real) $ ""

errorForIterType :: Type -> String
errorForIterType real =
    (showString "For loop header type error.\n").
    (msgShouldBeButIs (Int BNFC'NoPosition) real) $ ""

errorCondExprType :: Type -> String
errorCondExprType real =
    (showString "Condition isn't a logic value\n").
    (msgShouldBeButIs (Bool BNFC'NoPosition) real) $ ""

errorRetOutsideFun :: BNFC'Position -> String
errorRetOutsideFun pos =
    (showString "Return statement outside function block.\n").
    (prettyPositionAtShort pos) $ ""

errorJumpOutsideLoop :: Bool -> BNFC'Position -> String
errorJumpOutsideLoop isBreak pos =
    (if isBreak then showString "Break" else showString "Continue").
    (showString " statement outside a loop.\n").
    (prettyPositionAtShort pos) $ ""

msgNotExist :: BNFC'Position -> Ident -> ShowS
msgNotExist pos (Ident name) =
    (showString "`").
    (showString name).
    (showString "` doesn't exist.\n").
    (prettyPositionAtShort pos)

errorVarNotExist :: BNFC'Position -> Ident -> String
errorVarNotExist pos name =
    (showString "Variable ").
    (msgNotExist pos name) $ ""

errorFunNotExist :: BNFC'Position -> Ident -> String
errorFunNotExist pos name =
    (showString "Function ").
    (msgNotExist pos name) $ ""

errorFunAppArgCount ::
    BNFC'Position -> Ident -> Int -> Int -> String
errorFunAppArgCount pos (Ident name) expected real =
    (showString "Arguments count of `").
    (showString name).
    (showString "` doesn't match application.\n").

    (showString "\tFunction declaration count = ").
    (shows expected).
    (showString "\n").

    (showString "\tFunction application count = ").
    (shows real).
    (showString "\n").
    
    (prettyPositionAtShort pos) $ ""

errorFunAppArgType :: BNFC'Position -> Ident -> Type -> Type -> String
errorFunAppArgType pos (Ident funname) expected real =
    (showString "Function `").
    (showString funname).
    (showString "` application").
    (prettyPositionAt True pos).
    (showString " uses argument with a wrong type.\n").
    (msgShouldBeButIs expected real) $ ""

errorUnaryOp :: BNFC'Position -> Type -> Type -> String
errorUnaryOp pos expected real =
    (showString "Unary ").
    (msgOperatorError pos expected real) $ ""

errorBinaryOp :: BNFC'Position -> Type -> Type -> String
errorBinaryOp pos expected real =
    (showString "Binary ").
    (msgOperatorError pos expected real) $ ""

msgROVarAction :: String -> Ident -> Type -> Type -> String
msgROVarAction action (Ident name) prev next =
    (showString "Read-only variable `").
    (showString name).
    (showString "` ").
    (showString action).
    (prettyPositionAt True $ hasPosition next).
    (showString "\n").

    (showString "\tVariable has been declared").
    (prettyPositionAt True $ hasPosition prev) $ ""

errorROVarOverride :: Ident -> Type -> Type -> String
errorROVarOverride = msgROVarAction "overridden"

errorROVarAssignment :: Ident -> Type -> Type -> String
errorROVarAssignment = msgROVarAction "assigned to"
