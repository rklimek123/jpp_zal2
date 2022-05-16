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

all : Imper

# Rules for building the parser.

%.hs : %.y
	${HAPPY} ${HAPPY_OPTS} $<

%.hs : %.x
	${ALEX} ${ALEX_OPTS} $<

Imper : AbsImper.hs LexImper.hs ParImper.hs PrintImper.hs CommonImper.hs ErrorImper.hs TypecheckImper.hs InterpretImper.hs Imper.hs
	${GHC} ${GHC_OPTS} $@

# Rules for cleaning generated files.

clean :
	-rm -f *.hi *.o *.log *.aux *.dvi

distclean : clean
	-rm -f ComposOp.hs ComposOp.hs.bak ErrM.hs ErrM.hs.bak LayoutImper.hs LayoutImper.hs.bak ParImper.y ParImper.y.bak SkelImper.hs SkelImper.hs.bak XMLImper.hs XMLImper.hs.bak ASTImper.agda ASTImper.agda.bak ParserImper.agda ParserImper.agda.bak IOLib.agda IOLib.agda.bak Main.agda Main.agda.bak Imper.dtd Imper.dtd.bak TestImper ParDataImper.h


# EOF
