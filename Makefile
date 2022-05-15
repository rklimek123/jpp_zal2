## File generated by the BNF Converter (bnfc 2.9.4).

# Makefile for building the parser and test program.

GHC        = ghc
HAPPY      = happy
HAPPY_OPTS = --array --info --ghc --coerce
ALEX       = alex
ALEX_OPTS  = --ghc

# List of goals not corresponding to file names.

.PHONY : all clean distclean

# Default goal.

all : TestImper

# Rules for building the parser.

AbsImper.hs LexImper.x ParImper.y PrintImper.hs TestImper.hs : Imper.cf
	bnfc --haskell --functor Imper.cf

%.hs : %.y
	${HAPPY} ${HAPPY_OPTS} $<

%.hs : %.x
	${ALEX} ${ALEX_OPTS} $<

TestImper : AbsImper.hs LexImper.hs ParImper.hs PrintImper.hs TestImper.hs
	${GHC} ${GHC_OPTS} $@

# Rules for cleaning generated files.

clean :
	-rm -f *.hi *.o *.log *.aux *.dvi

distclean : clean
	-rm -f AbsImper.hs AbsImper.hs.bak ComposOp.hs ComposOp.hs.bak DocImper.txt DocImper.txt.bak ErrM.hs ErrM.hs.bak LayoutImper.hs LayoutImper.hs.bak LexImper.x LexImper.x.bak ParImper.y ParImper.y.bak PrintImper.hs PrintImper.hs.bak SkelImper.hs SkelImper.hs.bak TestImper.hs TestImper.hs.bak XMLImper.hs XMLImper.hs.bak ASTImper.agda ASTImper.agda.bak ParserImper.agda ParserImper.agda.bak IOLib.agda IOLib.agda.bak Main.agda Main.agda.bak Imper.dtd Imper.dtd.bak TestImper LexImper.hs ParImper.hs ParImper.info ParDataImper.hs Makefile


# EOF
