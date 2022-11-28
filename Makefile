.POSIX:

CFLAGS+=-std=c99 -Wall -Wpedantic

-include config.mk

.PHONY: all
all: pax

.PHONY: clean
clean:
	rm -f pax
