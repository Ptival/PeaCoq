PROGS=$(wildcard *.c)
EXECS=$(addsuffix .exec,$(PROGS))

CC=gcc

all: $(EXECS)

%.c.exec: %.c
	$(CC) $< -o $@

clean:
	rm *.exec

.PHONY: all clean
