EPISODES=$(wildcard E*.v)

all: $(EPISODES:.v=.glob)
	coqdoc --short $(EPISODES)
	./post-process.py

%.glob: %.v
	coqc $<

clean:
	rm -f *.glob *.vo coqdoc.css E*.html

.PHONY: all clean
