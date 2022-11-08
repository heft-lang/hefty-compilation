SRC := src
SCT := $(SRC)/sections

PDFLATEX = pdflatex -output-directory build/ -interaction=nonstopmode -file-line-error
LATEXMK  = latexmk -r $(SRC)/latexmkrc

# SOURCES := $(patsubst %.lagda,%.tex,$(wildcard $(SCT)/*.lagda))

all: document.pdf 

document.pdf: build build/document.tex src/references.bib # $(SOURCES) src/references.bib
	$(PDFLATEX) build/document.tex
	bibtex build/document
	$(PDFLATEX) build/document.tex
	$(PDFLATEX) build/document.tex
	cp build/document.pdf document.pdf

# Quick 'n dirty build, intended for use with watch script
quick: build build/document.tex # $(SOURCES)
	$(PDFLATEX) build/document.tex
	cp build/document.pdf document.pdf

build/document.tex: $(SRC)/document.tex
	cp $(SRC)/document.tex build/document.tex

# %.tex: %.lagda
# 	agda -i $(SRC) --latex --latex-dir=src $<

build:
	mkdir $@

clean:
	$(LATEXMK) -C .
	rm -f document.pdf
	rm -rf build
	rm -r $(SCT)/*.tex
.PHONY: all clean
