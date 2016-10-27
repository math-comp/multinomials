# -*- Makefile -*-

# --------------------------------------------------------------------
NAME     := SsrMultinomials
SUBDIRS  :=
COQFILES := \
	finmap/finmap.v \
	finmap/lattice.v \
	finmap/multiset.v \
	src/xfinmap.v \
	src/ssrcomplements.v \
	src/monalg.v \
	src/freeg.v \
	src/mpoly.v

ifeq ($(SSR_TOP),)
INCFLAGS := -R 3rdparty $(NAME)
SUBDIRS  +=
COQFILES += $(wildcard 3rdparty/*.v)
else
INCFLAGS := -I ${SSR_TOP}/ -R ${SSR_TOP} mathcomp
SUBDIRS  +=
COQFILES +=
endif

INCFLAGS += -R finmap $(NAME) -R src $(NAME)

include Makefile.common

# --------------------------------------------------------------------
.PHONY: install

install:
	$(MAKE) -f Makefile.coq install

# --------------------------------------------------------------------
this-clean::
	rm -f *.glob *.d *.vo

this-distclean::
	rm -f $(shell find . -name '*~')

# --------------------------------------------------------------------
.PHONY: fix-script

fix-script:
	scripts/coq-compat --coqc="$(COQC)" $(COQFILES)

# --------------------------------------------------------------------
.PHONY: count dist

# --------------------------------------------------------------------
DISTDIR = multinomials-ssr
TAROPT  = --posix --owner=0 --group=0

dist:
	if [ -e $(DISTDIR) ]; then rm -rf $(DISTDIR); fi
	./scripts/distribution.py $(DISTDIR) MANIFEST
	BZIP2=-9 tar $(TAROPT) -cjf $(DISTDIR).tar.bz2 $(DISTDIR)
	rm -rf $(DISTDIR)

count:
	@coqwc $(COQFILES) | tail -1 | \
	  awk '{printf ("%d (spec=%d+proof=%d)\n", $$1+$$2, $$1, $$2)}'
