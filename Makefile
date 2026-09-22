TEX := $(wildcard notes/*.tex)
PDF := $(TEX:.tex=.pdf)

all: $(PDF)

notes/%.pdf: notes/%.tex
	tectonic -o notes $<

clean:
	rm -f notes/*.aux notes/*.log notes/*.out

.PHONY: all clean
