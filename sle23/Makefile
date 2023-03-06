all: build/ build/output.pdf

build/:
	mkdir  -p build

build/output.tex: document.tex
	lhs2tex document.tex -o build/output.tex
	sed -i '' 's/\\usepackage{amssymb}//' build/output.tex

build/output.pdf: build/output.tex
	latexmk -pdf -pdflatex="pdflatex -interaction=nonstopmode" -use-make build/output.tex -jobname=build/output
clean:
	rm -r build