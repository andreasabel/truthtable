# Makefile for TYPES-post 2020

destdir=$(HOME)/public_html

# commands
bibtool=bibtool -- 'preserve.key.case = ON' \
	  -- 'print.use.tab = OFF' \
	  -- 'check.double = ON' \
	  -- 'check.double.delete = ON' \
	  -- 'delete.field = { abstract }' \
	  -- 'delete.field = { dvi }' \
	  -- 'delete.field = { postscript }' \
	  -- 'delete.field = { pdf }' \
	  -- 'delete.field = { month }' \
	  -- 'delete.field = { isbn }' \
	  -- 'delete.field = { note }'
#	  -- 'delete.field = { editor }'
#	  -- 'delete.field = { doi }' \

catcfg=sed -e "s/%.*//g" <
latex=latex
pdflatex=pdflatex
bibliography=medium.bib

files=lipics-v2021.cls Makefile \
  cc-by.pdf lipics-logo-bw.pdf orcid.pdf \
  types-post2020.tex sat.tex

.PHONY : default add all pack ship debugMake html

.PRECIOUS : %.dvi %.ps %.gz %.pdf %.tex

default : types-post2020.pdf

all : types-post2020.pdf

pack : types-post2020.zip

types-post2020.zip : types-post2020.pdf $(files) types-post2020.bbl auto-types-post2020.bib
	zip $@ $^

sat.pdf : types-post2020.pdf Makefile
	pdfjam -o $@ $< 18-

# types-post2020
##################################################################

# types-post2020.pdf: types-post2020.tex $(files)
# 	latexmk -f -pdf types-post2020.tex

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
types-post2020_aux : types-post2020.tex $(files)
	-$(pdflatex) $<;
	touch $@;

# then, run bibtex
types-post2020.bbl : types-post2020_aux auto-types-post2020.bib
	-bibtex types-post2020;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
types-post2020.pdf : types-post2020.bbl
	-$(pdflatex) types-post2020.tex;
	$(pdflatex) types-post2020.tex;

# auto-types-post2020.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-types-post2020.bib : types-post2020_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x types-post2020.aux -i $(bibliography) >> $@;
endif
endif

# types-post2020-long
##################################################################

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
types-post2020-long_aux : types-post2020-long.tex $(files)
	$(pdflatex) types-post2020-long.tex;
	touch $@;

# then, run bibtex
types-post2020-long.bbl : types-post2020-long_aux auto-types-post2020.bib
	-bibtex types-post2020-long;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
types-post2020-long.pdf : types-post2020-long.bbl
	$(pdflatex) types-post2020-long.tex;
	$(pdflatex) types-post2020-long.tex;

# auto-types-post2020-long.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-types-post2020-long.bib : types-post2020-long_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x types-post2020-long.aux -i $(bibliography) >> $@;
endif
endif



# Templates (reverted back to simple templates)


talk% : talk%.pdf
	cp -p $? $(destdir)/;
	touch $@;

talk%.pdf : talk%.tex
	pdflatex $<;


%.tex : %.lhs
	lhs2TeX --poly -i lhs2TeX.fmt $< > $@
# /usr/local/share/lhs2tex-1.13/

% :  %.pdf # %.dvi %.ps.gz # %.tar.gz
	cp -p $? $(destdir)/;
	touch $@;

%.pdf : %.dvi
	pdflatex $*.tex;

%.ps  : %.dvi
	dvips -o $@ $<;

%.gz : %
	cat $< | gzip > $@

## does not work since $ is evaluated before %
#%.tar : %.cfg $(shell cat %.cfg)
#	echo $?


#EOF
