# -*- Makefile -*-

# --------------------------------------------------------------------
DUNEOPTS ?=
DUNE     := dune $(DUNEOPTS)

# --------------------------------------------------------------------
.PHONY: default build clean

default: build

build:
	$(DUNE) build

clean:
	$(DUNE) clean
