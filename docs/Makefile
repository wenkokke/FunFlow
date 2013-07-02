FMT := $(shell find . -name "*.fmt")
LTX := $(shell find . -name "*.ltx")
STY := $(shell find . -name "*.sty")

all : apa.pdf apa-nocolour.pdf

apa.pdf : apa.tex # apa.bib
	svn info | grep 'Revision'          | sed 's/.*\: //' >  REVISION
	svn info | grep 'Last Changed Date' | sed 's/.*(/(/'  >> REVISION
	pdflatex -halt-on-error apa.tex
#	bibtex apa
#	pdflatex -halt-on-error apa.tex
	sh -c ' \
	  i=1; \
	  while [ $$i -lt 5 ] && ( \
	    grep -c "Rerun" apa.log \
	    || grep -c "undefined citations" apa.log \
	    || grep -c "undefined references" apa.log ); \
	  do pdflatex -halt-on-error apa.tex; \
	     i=`expr $$i + 1`; \
	     done; \
          echo "Iterations: $$i"'

apa.tex : $(LTX) $(STY) $(FMT)
	lhs2TeX --poly --set=colour --set=draft apa.ltx > apa.tex

apa-nocolour.pdf : apa-nocolour.tex # apa.bib
	svn info | grep 'Revision'          | sed 's/.*\: //' >  REVISION
	svn info | grep 'Last Changed Date' | sed 's/.*(/(/'  >> REVISION
	pdflatex -halt-on-error apa-nocolour.tex
#	bibtex apa-nocolour
#	pdflatex -halt-on-error apa-nocolour.tex
	sh -c ' \
	  i=1; \
	  while [ $$i -lt 5 ] && ( \
	    grep -c "Rerun" apa-nocolour.log \
	    || grep -c "undefined citations" apa-nocolour.log \
	    || grep -c "undefined references" apa-nocolour.log ); \
	  do pdflatex -halt-on-error apa-nocolour.tex; \
	     i=`expr $$i + 1`; \
	     done; \
          echo "Iterations: $$i"'

apa-nocolour.tex : $(LTX) $(STY) $(FMT)
	lhs2TeX --poly --set=draft apa.ltx > apa-nocolour.tex

clean :
	rm -f REVISION *~ *.aux *.bbl *.blg *.log *.out *.ptb *.tex

clean-all : clean
	rm -f apa.pdf apa-nocolour.pdf

from-scratch : clean-all all

from-scratch-and-clean : clean-all all
	rm -f REVISION *~ *.aux *.bbl *.blg *.log *.out *.ptb *.tex

.PHONY : clean clean-all from-scratch from-scratch-and-clean