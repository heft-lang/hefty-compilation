all: build/ build/output.pdf

build/:
	mkdir  -p build

build/output.tex: document.lhs
	lhs2tex document.lhs -o build/output.tex
	sed -i '' 's/\\usepackage{amssymb}//' build/output.tex

build/output.pdf: build/output.tex
	latexmk -pdf -pdflatex="pdflatex -interaction=nonstopmode" -use-make build/output.tex -jobname=build/output
clean:
	rm -r build