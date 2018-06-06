ACLOCAL_AMFLAGS = -I m4

BINARCHDIR = bin/$(GAPARCH)
GAPINSTALLLIB = $(BINARCHDIR)/cvec.so

lib_LTLIBRARIES = cvec.la

cvec_la_SOURCES = src/cvec.c
cvec_la_CPPFLAGS = $(GAP_CPPFLAGS)
cvec_la_CFLAGS = $(GAP_CFLAGS)
cvec_la_LDFLAGS = $(GAP_LDFLAGS) -module -avoid-version
if SYS_IS_CYGWIN
cvec_la_LDFLAGS += -no-undefined -version-info 0:0:0 -Wl,$(GAPROOT)/bin/$(GAPARCH)/gap.dll
endif

all-local: $(GAPINSTALLLIB)

$(GAPINSTALLLIB): cvec.la
	$(mkdir_p) $(top_srcdir)/$(BINARCHDIR)
if SYS_IS_CYGWIN
	cp .libs/cvec.dll $(GAPINSTALLLIB)
else
	cp .libs/cvec.so $(GAPINSTALLLIB)
endif

clean-local:
	rm -f $(GAPINSTALLLIB)

distclean-local:
	rm -rf bin/*
	(cd doc ; ./clean)

doc:
	(echo 'Read("makedoc.g");' | $(GAPROOT)/bin/gap.sh -A -q)

.PHONY: doc
