MAIN = main
TEX_DEPS = $(MAIN).tex references.bib lib.tex comments.sty \
           intro.tex overview.tex design.tex implementation.tex \
           evaluation.tex related.tex conclusion.tex \
           $(wildcard figures/*.tex)

all: $(MAIN).pdf

$(MAIN).pdf: $(TEX_DEPS)
	latexmk -pdf $(MAIN).tex

clean:
	latexmk -C $(MAIN).tex
