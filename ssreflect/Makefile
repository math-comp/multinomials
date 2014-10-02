# -*- Makefile -*-

# --------------------------------------------------------------------
INCFLAGS := -I .
COQFILES := ssreflect.mllib ssreflect.ml4 ssrmatching.ml4 ssrmatching.mli
COQFILES += $(wildcard *.v)

# ------------------------------------------------------------------------
ifeq ($(wildcard ssreflect.ml4),)
# No local copy of SSReflect.
clean:
	@true

distclean:
	@true

build:
	@true

config:
	@true
else
# A copy of SSReflect has been installed
include ../Makefile.common

this-distclean::
	rm -f *.v *.ml*
endif
