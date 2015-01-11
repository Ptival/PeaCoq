COQC=coqc
COQDOC=coqdoc

WEB_ACCT=ztatlock@recycle.cs.washington.edu
WEB_PATH=/cse/web/courses/cse505/15wi

EPISODES=$(wildcard e[0-9][0-9])
MATERIALS=$(patsubst %,%/materials.html,$(EPISODES))

# lecture coqdoc
EPISODES_V=$(wildcard e[0-9][0-9]/*.v)
EPISODES_VOBJ=$(patsubst %.v,%.vo,$(EPISODES_V))
EPISODES_GLOB=$(patsubst %.v,%.glob,$(EPISODES_V))
EPISODES_HTML=$(patsubst %.v,%.html,$(EPISODES_V))
EPISODES_CSS=$(patsubst %,%/coqdoc.css,$(EPISODES))

all: $(EPISODES_HTML)
	for e in $(EPISODES); do ./mkmaterials.sh $$e; done

%.html: %.v
	$(COQC) $<
	$(COQDOC) --short --no-index --output $@ $<

publish:
	chmod -R a+r *
	rsync --recursive . "$(WEB_ACCT):$(WEB_PATH)"

clean:
	rm -f $(MATERIALS)
	rm -f $(EPISODES_VOBJ)
	rm -f $(EPISODES_GLOB)
	rm -f $(EPISODES_HTML)
	rm -f $(EPISODES_CSS)

.PHONY: all publish clean
