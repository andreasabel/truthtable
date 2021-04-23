# Makefile for contnorm

destdir=$(HOME)/public_html

# commands
bibtool=bibtool -- 'preserve.key.case = ON' \
	  -- 'check.double = ON' \
	  -- 'check.double.delete = ON' \
	  -- 'delete.field = { abstract }' \
	  -- 'delete.field = { dvi }' \
	  -- 'delete.field = { postscript }' \
	  -- 'delete.field = { pdf }' \
	  -- 'delete.field = { month }' \
	  -- 'delete.field = { isbn }' \
	  -- 'delete.field = { doi }'

deletemore =
# deletemore = \
#   -- 'delete.field = { editor }' \
#   -- 'delete.field = { pages }'

catcfg=sed -e "s/%.*//g" <
latex=latex
pdflatex=pdflatex
bibliography=medium.bib
sedfile=postprocess.sed

files=

types21tex=types21.tex
typesbibliography=all.bib


default : types21.pdf # talkTYPES21.pdf talkTYPES21-with-notes.pdf talkTYPES21.zip

all : default ship

ship : $(destdir)/types21.pdf

$(destdir)/types21.pdf : types21.pdf
	cp -p $< $@

shipTalk : $(destdir)/talkTYPES2120.pdf

$(destdir)/talkTYPES2120.pdf : talkTYPES2120.pdf
	cp -p $< $@

#$(destdir)/types21.lagda : types21.lagda
#	cp -p $< $@

pack : types21.zip

types21.zip : types21.tex types21.bbl easychair.cls macros.tex auto-types21.bib
	zip $@ $^

talkTYPES21.zip : Makefile talkTYPES21.tex talkTYPES21.pdf talkTYPES21-with-notes.tex talkTYPES21-with-notes.pdf
	zip $@ $^

# types21
##################################################################

# types21.tex : latex/types21.tex $(sedfile)
# 	sed --file=$(sedfile) < $< > $@

# latex/types21.tex : types21.lagda
#	agda --latex -i. -i$(stdlib) $<

# types21.pdf : types21.lagda
#	pdflatex $<

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
auto-types21.aux : $(types21tex) $(files) Makefile
	$(pdflatex) $(types21tex);
	cp types21.aux $@;

# then, run bibtex
auto-types21.bbl : auto-types21.aux auto-types21.bib
	-bibtex auto-types21;

types21.bbl : auto-types21.bbl
	sed -e 's/volume/vol\./g' -e 's/URL //g' < $< > $@

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
types21.pdf : types21.bbl
	$(pdflatex) $(types21tex);
	$(pdflatex) $(types21tex);

# auto-types21.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(typesbibliography)),)
auto-types21.bib : auto-types21.aux $(typesbibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) $(deletemore) -x types21.aux -i $(typesbibliography) >> $@;
endif
endif

# Templates (reverted back to simple templates)


talk% : talk%.pdf
	cp -p $? $(destdir)/;
	touch $@;

talk%.pdf : talk%.tex
	pdflatex $<;

# cleaning

clean :
	-rm *.log *.aux *.blg *.out *_aux *.bbl

veryclean : clean
	-rm auto-*

# EOF
