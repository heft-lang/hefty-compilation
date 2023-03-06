all: build/ build/output.pdf

build/:
	mkdir  -p build

build/output.tex: document.tex
	lhs2tex document.tex -o build/output.tex
	sed -i '' 's/\\usepackage{amssymb}//' build/output.tex

build/output.pdf: build/output.tex
	pdflatex -output-directory=build build/output.tex
	pdflatex -output-directory=build build/output.tex

clean:
	rm -r build