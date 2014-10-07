# -*- Makefile -*-

# --------------------------------------------------------------------
INCFLAGS := -I .
SUBDIRS  :=

ifeq ($(SSR_TOP),)
INCFLAGS += -I ssreflect -I ssreflect-extra 
SUBDIRS  += ssreflect ssreflect-extra
else
INCFLAGS += -I ${SSR_TOP}/ssreflect/${COQBRANCH}/src -R ${SSR_TOP}/theories/ Ssreflect
SUBDIRS  +=
endif

COQFILES = poset.v freeg.v mpoly.v

include Makefile.common

# --------------------------------------------------------------------
SSRV   = 1.5
SSRTMP = ssreflect-tmp
SSRURL = http://ssr.msr-inria.inria.fr/FTP/ssreflect-$(SSRV).tar.gz
MTHURL = http://ssr.msr-inria.inria.fr/FTP/mathcomp-$(SSRV).tar.gz

.PHONY: get-ssr

get-ssr:
	$(MAKE) -C ssreflect this-distclean
	[ ! -e $(SSRTMP) ] || rm -rf $(SSRTMP); mkdir $(SSRTMP)
	wget -P $(SSRTMP) $(SSRURL)
	wget -P $(SSRTMP) $(MTHURL)
	tar -C $(SSRTMP) -xof $(SSRTMP)/ssreflect-$(SSRV).tar.gz
	tar -C $(SSRTMP) -xof $(SSRTMP)/mathcomp-$(SSRV).tar.gz
	cp $(SSRTMP)/ssreflect-$(SSRV)/src/* $(TOP)/ssreflect/
	cp $(SSRTMP)/ssreflect-$(SSRV)/theories/* $(TOP)/ssreflect/
	cd ssreflect && ../scripts/add-ssr.py ../$(SSRTMP)/mathcomp-$(SSRV)/theories ../*.v
	rm -rf ssreflect-tmp/

# --------------------------------------------------------------------
this-clean::
	rm -f *.glob *.d *.vo

this-distclean::
	rm -f $(shell find . -name '*~')

# --------------------------------------------------------------------
.PHONY: count dist

# --------------------------------------------------------------------
DISTDIR = ecssr
TAROPT  = --posix --owner=0 --group=0

dist:
	if [ -e $(DISTDIR) ]; then rm -rf $(DISTDIR); fi
	./scripts/distribution.py $(DISTDIR) MANIFEST
	BZIP2=-9 tar $(TAROPT) -cjf $(DISTDIR).tar.bz2 $(TAROPT) $(DISTDIR)
	rm -rf $(DISTDIR)

count:
	@coqwc $(COQFILES) | tail -1 | \
     awk '{printf ("%d (spec=%d+proof=%d)\n", $$1+$$2, $$1, $$2)}'
