LEC=$(wildcard *.v)

all: $(LEC:.v=.glob)
	coqdoc --lib-name Episode $(LEC)

%.glob: %.v
	coqc $<

clean:
	rm -f *.glob *.vo *.css *.html

.PHONY: all clean
