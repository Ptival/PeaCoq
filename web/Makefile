BUILDDIR=build
SRCDIR=src

FILES=$(notdir $(wildcard $(SRCDIR)/*.js))
SOURCES=$(addprefix $(SRCDIR)/, $(FILES))
TARGETS=$(addprefix $(BUILDDIR)/, $(FILES))
TARGET=main.js

all: $(TARGET)

$(TARGET): $(TARGETS)
	browserify -d $(BUILDDIR)/lecture-flow.js > $(TARGET)

$(BUILDDIR)/%.js : $(SRCDIR)/%.js
	jsx --strip-types $^ > $@

print-%:
	@echo '$*=$($*)'

clean:
	rm $(TARGETS) $(TARGET)

