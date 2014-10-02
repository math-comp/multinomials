# -*- Makefile -*-

# --------------------------------------------------------------------
INCFLAGS := -I .
COQFILES := ssreflect.mllib ssreflect.ml4 ssrmatching.ml4 ssrmatching.mli
COQFILES += $(wildcard *.v)
PATCHED  := $(patsubst %.base,%,$(wildcard *.v.base))

# ------------------------------------------------------------------------
-include ../Makefile.common
