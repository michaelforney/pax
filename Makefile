.POSIX:

CFLAGS+=-std=c99 -Wall -Wpedantic

.PHONY: all
all: pax

.PHONY: clean
clean:
	rm -f pax
