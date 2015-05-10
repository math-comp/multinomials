# -*- Makefile -*-

# --------------------------------------------------------------------
NAME     := SsrMultinomials
SUBDIRS  :=
COQFILES := \
	src/ssrcomplements.v \
	src/poset.v \
	src/freeg.v \
	src/mpoly.v

ifeq ($(SSR_TOP),)
INCFLAGS := -I ssreflect -R 3rdparty $(NAME)
SUBDIRS  += ssreflect
COQFILES += $(wildcard 3rdparty/*.v)
else
INCFLAGS := -I ${SSR_TOP}/ssreflect/${COQBRANCH}/src -R ${SSR_TOP}/theories/ Ssreflect
SUBDIRS  +=
endif

INCFLAGS += -R src $(NAME)

include Makefile.common

# --------------------------------------------------------------------
SSRV   = 1.5
SSRTMP = ssreflect-tmp
SSRURL = http://ssr.msr-inria.inria.fr/FTP/ssreflect-$(SSRV).tar.gz
MTHURL = http://ssr.msr-inria.inria.fr/FTP/mathcomp-$(SSRV).tar.gz

.PHONY: get-ssr

get-ssr:
	$(MAKE) -C ssreflect distclean
	[ ! -e $(SSRTMP) ] || rm -rf $(SSRTMP); mkdir $(SSRTMP)
	wget -P $(SSRTMP) $(SSRURL)
	wget -P $(SSRTMP) $(MTHURL)
	tar -C $(SSRTMP) -xof $(SSRTMP)/ssreflect-$(SSRV).tar.gz
	tar -C $(SSRTMP) -xof $(SSRTMP)/mathcomp-$(SSRV).tar.gz
	cp $(SSRTMP)/ssreflect-$(SSRV)/src/* $(TOP)/ssreflect/
	cp $(SSRTMP)/ssreflect-$(SSRV)/theories/* $(TOP)/ssreflect/
	cd ssreflect && ../scripts/add-ssr.py ../$(SSRTMP)/mathcomp-$(SSRV)/theories ../src/*.v
	rm -rf ssreflect-tmp/

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
.PHONY: count dist

# --------------------------------------------------------------------
DISTDIR = multinomials-ssr
TAROPT  = --posix --owner=0 --group=0

dist:
	if [ -e $(DISTDIR) ]; then rm -rf $(DISTDIR); fi
	./scripts/distribution.py $(DISTDIR) MANIFEST
	BZIP2=-9 tar $(TAROPT) -cjf $(DISTDIR).tar.bz2 $(TAROPT) $(DISTDIR)
	rm -rf $(DISTDIR)

count:
	@coqwc $(COQFILES) | tail -1 | \
     awk '{printf ("%d (spec=%d+proof=%d)\n", $$1+$$2, $$1, $$2)}'
