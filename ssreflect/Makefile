# -*- Makefile -*-

# --------------------------------------------------------------------
INCFLAGS := -I .
COQFILES := ssreflect.mllib ssreflect.ml4 ssrmatching.ml4 ssrmatching.mli
COQFILES += $(wildcard *.v)
PATCHED  := $(patsubst %.base,%,$(wildcard *.v.base))

# ------------------------------------------------------------------------
-include ../Makefile.common

# --------------------------------------------------------------------
.PHONY: create-patches

create-patches:
	@for i in $(PATCHED); do            \
	  echo "Diff'ing $$i...";           \
	  diff -u $$i.base $$i > $$i.patch; \
	  [ $$? -le 1 ] || false;           \
	done
