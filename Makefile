# Makefile for building the parser and interpreter.

GHC        = ghc
HAPPY      = happy
HAPPY_OPTS = --array --info --ghc --coerce
ALEX       = alex
ALEX_OPTS  = --ghc

# List of goals not corresponding to file names.

.PHONY : all clean

# Default goal.

all : interpreter

# Rules for building the parser.

%.hs : %.y
	${HAPPY} ${HAPPY_OPTS} $<

%.hs : %.x
	${ALEX} ${ALEX_OPTS} $<

interpreter : AbsImper.hs LexImper.hs ParImper.hs PrintImper.hs ErrorImper.hs TypecheckImper.hs InterpretImper.hs Imper.hs
	${GHC} ${GHC_OPTS} Imper -o interpreter

# Rules for cleaning generated files.

clean :
	-rm -f *.hi *.o *.log *.aux *.dvi *.bak interpreter

# EOF
