MODULES_NODOC := Axioms Tactics MoreSpecif DepList
MODULES_PROSE := Intro
MODULES_CODE  := StackMachine InductiveTypes Predicates Coinductive Subset \
	MoreDep DataStruct Equality Generic Universes Match Reflection \
	Large Firstorder DeBruijn Hoas Interps Extensional Intensional OpSem
MODULES_DOC   := $(MODULES_PROSE) $(MODULES_CODE)
MODULES       := $(MODULES_NODOC) $(MODULES_DOC)
VS            := $(MODULES:%=src/%.v)
VS_DOC        := $(MODULES_DOC:%=%.v)
TEMPLATES     := $(MODULES_CODE:%=templates/%.v)

.PHONY: coq clean doc dvi html templates install cpdt.tgz

coq: Makefile.coq
	make -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) \
		COQC = "coqc -I src" \
		COQDEP = "coqdep -I src" \
		-o Makefile.coq

clean:: Makefile.coq
	make -f Makefile.coq clean
	rm -f Makefile.coq .depend cpdt.tgz \
		latex/*.sty latex/cpdt.* templates/*.v
	rm -f *.aux *.dvi *.log

doc: latex/cpdt.dvi latex/cpdt.pdf html

latex/cpdt.tex: Makefile $(VS)
	cd src ; coqdoc --interpolate --latex -s $(VS_DOC) \
		-p "\usepackage{url,amsmath,amssymb}" \
		-p "\title{Certified Programming with Dependent Types}" \
		-p "\author{Adam Chlipala}" \
		-p "\iffalse" \
		-o ../latex/cpdt.tex

latex/%.tex: src/%.v
	coqdoc --interpolate --latex -s \
		-p "\usepackage{url,amsmath,amssymb}" \
		$< -o $@

latex/%.dvi: latex/%.tex
	cd latex ; latex $* ; latex $*

latex/%.pdf: latex/%.dvi
	cd latex ; pdflatex $* ; pdflatex $*

html: Makefile $(VS) src/toc.html
	mkdir -p html
	cd src ; coqdoc --interpolate $(VS_DOC) \
		-d ../html
	cp src/toc.html html/

dvi:
	xdvi latex/cpdt

templates: $(TEMPLATES)

templates/%.v: src/%.v tools/make_template.ml
	ocaml tools/make_template.ml <$< >$@

cpdt.tgz:
	hg archive -t tgz $@

install: cpdt.tgz latex/cpdt.pdf html
	cp cpdt.tgz staging/
	cp latex/cpdt.pdf staging/
	cp -R html staging/
	rsync -az --exclude '*~' staging/* schizomaniac.net:sites/chlipala/adam/cpdt/
