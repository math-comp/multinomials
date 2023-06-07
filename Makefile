# -*- Makefile -*-

# --------------------------------------------------------------------
DUNEOPTS ?=
DUNE     := dune $(DUNEOPTS)

# --------------------------------------------------------------------
.PHONY: default build clean

default: build

build:
	$(DUNE) build

install:
	$(DUNE) install

clean:
	$(DUNE) clean
