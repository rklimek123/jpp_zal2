-- File generated by the BNF Converter (bnfc 2.9.4).

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

-- | Pretty-printer for PrintImper.

module PrintImper where

import Prelude
  ( ($), (.)
  , Bool(..), (==), (<)
  , Int, Integer, Double, (+), (-), (*)
  , String, (++)
  , ShowS, showChar, showString
  , all, elem, foldr, id, map, null, replicate, shows, span
  )
import Data.Char ( Char, isSpace )
import qualified AbsImper

-- | The top-level printing method.

printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 False (map ($ "") $ d []) ""
  where
  rend
    :: Int        -- ^ Indentation level.
    -> Bool       -- ^ Pending indentation to be output before next character?
    -> [String]
    -> ShowS
  rend i p = \case
      "["      :ts -> char '[' . rend i False ts
      "("      :ts -> char '(' . rend i False ts
      "{"      :ts -> onNewLine i     p . showChar   '{'  . new (i+1) ts
      "}" : ";":ts -> onNewLine (i-1) p . showString "};" . new (i-1) ts
      "}"      :ts -> onNewLine (i-1) p . showChar   '}'  . new (i-1) ts
      [";"]        -> char ';'
      ";"      :ts -> char ';' . new i ts
      t  : ts@(s:_) | closingOrPunctuation s
                   -> pending . showString t . rend i False ts
      t        :ts -> pending . space t      . rend i False ts
      []           -> id
    where
    -- Output character after pending indentation.
    char :: Char -> ShowS
    char c = pending . showChar c

    -- Output pending indentation.
    pending :: ShowS
    pending = if p then indent i else id

  -- Indentation (spaces) for given indentation level.
  indent :: Int -> ShowS
  indent i = replicateS (2*i) (showChar ' ')

  -- Continue rendering in new line with new indentation.
  new :: Int -> [String] -> ShowS
  new j ts = showChar '\n' . rend j True ts

  -- Make sure we are on a fresh line.
  onNewLine :: Int -> Bool -> ShowS
  onNewLine i p = (if p then id else showChar '\n') . indent i

  -- Separate given string from following text by a space (if needed).
  space :: String -> ShowS
  space t s =
    case (all isSpace t', null spc, null rest) of
      (True , _   , True ) -> []              -- remove trailing space
      (False, _   , True ) -> t'              -- remove trailing space
      (False, True, False) -> t' ++ ' ' : s   -- add space if none
      _                    -> t' ++ s
    where
      t'          = showString t []
      (spc, rest) = span isSpace s

  closingOrPunctuation :: String -> Bool
  closingOrPunctuation [c] = c `elem` closerOrPunct
  closingOrPunctuation _   = False

  closerOrPunct :: String
  closerOrPunct = ")],;"

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- | The printer class does the job.

class Print a where
  prt :: Int -> a -> Doc

instance {-# OVERLAPPABLE #-} Print a => Print [a] where
  prt i = concatD . map (prt i)

instance Print Char where
  prt _ c = doc (showChar '\'' . mkEsc '\'' c . showChar '\'')

instance Print String where
  prt _ = printString

printString :: String -> Doc
printString s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q = \case
  s | s == q -> showChar '\\' . showChar s
  '\\' -> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  s -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j < i then parenth else id

instance Print Integer where
  prt _ x = doc (shows x)

instance Print Double where
  prt _ x = doc (shows x)

instance Print AbsImper.Ident where
  prt _ (AbsImper.Ident i) = doc $ showString i
instance Print (AbsImper.Program' a) where
  prt i = \case
    AbsImper.Prog _ progstmts -> prPrec i 0 (concatD [prt 0 progstmts])

instance Print (AbsImper.ProgStmt' a) where
  prt i = \case
    AbsImper.FnDef _ id_ args block -> prPrec i 0 (concatD [doc (showString "fun"), prt 0 id_, doc (showString "("), prt 0 args, doc (showString ")"), prt 0 block, doc (showString ";")])
    AbsImper.ProgSt _ stmt -> prPrec i 0 (concatD [prt 0 stmt])

instance Print [AbsImper.ProgStmt' a] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print (AbsImper.Arg' a) where
  prt i = \case
    AbsImper.FnArg _ type_ id_ -> prPrec i 0 (concatD [prt 0 type_, prt 0 id_])

instance Print [AbsImper.Arg' a] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print (AbsImper.Block' a) where
  prt i = \case
    AbsImper.StBlock _ stmts -> prPrec i 0 (concatD [doc (showString "{"), prt 0 stmts, doc (showString "};")])

instance Print [AbsImper.Stmt' a] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print (AbsImper.Stmt' a) where
  prt i = \case
    AbsImper.Decl _ astmt -> prPrec i 0 (concatD [doc (showString "var"), prt 0 astmt, doc (showString ";")])
    AbsImper.DeclRO _ astmt -> prPrec i 0 (concatD [doc (showString "const"), prt 0 astmt, doc (showString ";")])
    AbsImper.AssStmt _ astmt -> prPrec i 0 (concatD [prt 0 astmt, doc (showString ";")])
    AbsImper.TupleAss _ tbox expr -> prPrec i 0 (concatD [prt 0 tbox, doc (showString ":="), prt 0 expr, doc (showString ";")])
    AbsImper.Cond _ ifbl elifbls -> prPrec i 0 (concatD [prt 0 ifbl, prt 0 elifbls])
    AbsImper.CondElse _ ifbl elifbls elsebl -> prPrec i 0 (concatD [prt 0 ifbl, prt 0 elifbls, prt 0 elsebl])
    AbsImper.For _ astmt expr block -> prPrec i 0 (concatD [doc (showString "for"), prt 0 astmt, doc (showString "to"), prt 0 expr, prt 0 block])
    AbsImper.While _ expr block -> prPrec i 0 (concatD [doc (showString "while"), doc (showString "("), prt 0 expr, doc (showString ")"), prt 0 block])
    AbsImper.Ret _ expr -> prPrec i 0 (concatD [doc (showString "return"), prt 0 expr, doc (showString ";")])
    AbsImper.Break _ -> prPrec i 0 (concatD [doc (showString "break"), doc (showString ";")])
    AbsImper.Continue _ -> prPrec i 0 (concatD [doc (showString "continue"), doc (showString ";")])
    AbsImper.Print _ expr -> prPrec i 0 (concatD [doc (showString "print"), prt 0 expr, doc (showString ";")])
    AbsImper.Skip _ -> prPrec i 0 (concatD [doc (showString "skip"), doc (showString ";")])
    AbsImper.SExp _ expr -> prPrec i 0 (concatD [prt 0 expr, doc (showString ";")])

instance Print (AbsImper.AStmt' a) where
  prt i = \case
    AbsImper.Ass _ id_ expr -> prPrec i 0 (concatD [prt 0 id_, doc (showString ":="), prt 0 expr])

instance Print (AbsImper.TBox' a) where
  prt i = \case
    AbsImper.TupleBox _ telems -> prPrec i 0 (concatD [doc (showString "("), prt 0 telems, doc (showString ")")])

instance Print (AbsImper.TElem' a) where
  prt i = \case
    AbsImper.TupleTup _ tbox -> prPrec i 0 (concatD [prt 0 tbox])
    AbsImper.TupleAtom _ id_ -> prPrec i 0 (concatD [prt 0 id_])
    AbsImper.TupleIgn _ -> prPrec i 0 (concatD [doc (showString "_")])

instance Print [AbsImper.TElem' a] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print (AbsImper.IfBl' a) where
  prt i = \case
    AbsImper.IfBlock _ expr block -> prPrec i 0 (concatD [doc (showString "if"), doc (showString "("), prt 0 expr, doc (showString ")"), prt 0 block])

instance Print (AbsImper.ElifBl' a) where
  prt i = \case
    AbsImper.ElifBlock _ expr block -> prPrec i 0 (concatD [doc (showString "elif"), doc (showString "("), prt 0 expr, doc (showString ")"), prt 0 block])

instance Print (AbsImper.ElseBl' a) where
  prt i = \case
    AbsImper.ElseBlock _ block -> prPrec i 0 (concatD [doc (showString "else"), prt 0 block])

instance Print [AbsImper.ElifBl' a] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print (AbsImper.Type' a) where
  prt i = \case
    AbsImper.Int _ -> prPrec i 0 (concatD [doc (showString "int")])
    AbsImper.Str _ -> prPrec i 0 (concatD [doc (showString "string")])
    AbsImper.Bool _ -> prPrec i 0 (concatD [doc (showString "bool")])
    AbsImper.Tuple _ types -> prPrec i 0 (concatD [doc (showString "("), prt 0 types, doc (showString ")")])

instance Print [AbsImper.Type' a] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print (AbsImper.Expr' a) where
  prt i = \case
    AbsImper.EVar _ id_ -> prPrec i 6 (concatD [prt 0 id_])
    AbsImper.ELitInt _ n -> prPrec i 6 (concatD [prt 0 n])
    AbsImper.ELitTrue _ -> prPrec i 6 (concatD [doc (showString "_T")])
    AbsImper.ELitFalse _ -> prPrec i 6 (concatD [doc (showString "_F")])
    AbsImper.ELitTuple _ exprs -> prPrec i 6 (concatD [doc (showString "("), prt 0 exprs, doc (showString ")")])
    AbsImper.EApp _ id_ exprs -> prPrec i 6 (concatD [prt 0 id_, doc (showString "("), prt 0 exprs, doc (showString ")")])
    AbsImper.EString _ str -> prPrec i 6 (concatD [printString str])
    AbsImper.Neg _ expr -> prPrec i 5 (concatD [doc (showString "-"), prt 6 expr])
    AbsImper.Not _ expr -> prPrec i 5 (concatD [doc (showString "!"), prt 6 expr])
    AbsImper.EMul _ expr1 mulop expr2 -> prPrec i 4 (concatD [prt 4 expr1, prt 0 mulop, prt 5 expr2])
    AbsImper.EAdd _ expr1 addop expr2 -> prPrec i 3 (concatD [prt 3 expr1, prt 0 addop, prt 4 expr2])
    AbsImper.ERel _ expr1 relop expr2 -> prPrec i 2 (concatD [prt 2 expr1, prt 0 relop, prt 3 expr2])
    AbsImper.EAnd _ expr1 expr2 -> prPrec i 1 (concatD [prt 2 expr1, doc (showString "&&"), prt 1 expr2])
    AbsImper.EOr _ expr1 expr2 -> prPrec i 0 (concatD [prt 1 expr1, doc (showString "||"), prt 0 expr2])

instance Print [AbsImper.Expr' a] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print (AbsImper.AddOp' a) where
  prt i = \case
    AbsImper.Plus _ -> prPrec i 0 (concatD [doc (showString "+")])
    AbsImper.Minus _ -> prPrec i 0 (concatD [doc (showString "-")])

instance Print (AbsImper.MulOp' a) where
  prt i = \case
    AbsImper.Times _ -> prPrec i 0 (concatD [doc (showString "*")])
    AbsImper.Div _ -> prPrec i 0 (concatD [doc (showString "/")])
    AbsImper.Mod _ -> prPrec i 0 (concatD [doc (showString "%")])

instance Print (AbsImper.RelOp' a) where
  prt i = \case
    AbsImper.LTH _ -> prPrec i 0 (concatD [doc (showString "<")])
    AbsImper.LE _ -> prPrec i 0 (concatD [doc (showString "<=")])
    AbsImper.GTH _ -> prPrec i 0 (concatD [doc (showString ">")])
    AbsImper.GE _ -> prPrec i 0 (concatD [doc (showString ">=")])
    AbsImper.EQU _ -> prPrec i 0 (concatD [doc (showString "==")])
    AbsImper.NE _ -> prPrec i 0 (concatD [doc (showString "!=")])
