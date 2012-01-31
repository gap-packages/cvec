ACLOCAL_AMFLAGS = -I m4

SUBDIRS = 

BINARCHDIR = bin/$(GAPARCH)
GAPINSTALLLIB = $(abs_top_srcdir)/$(BINARCHDIR)/cvec.so

lib_LTLIBRARIES = cvec.la

cvec_la_SOURCES = src/cvec.c
cvec_la_CPPFLAGS = $(GAP_CPPFLAGS) -DCONFIG_H
# Note that the latter is only for GAP 4.4.12
cvec_la_LDFLAGS = -module -avoid-version
if SYS_IS_CYGWIN
cvec_la_LDFLAGS += -no-undefined -version-info 0:0:0 -Wl,$(GAPROOT)/bin/$(GAPARCH)/gap.dll
endif

all-local: cvec.la install-libLTLIBRARIES
#	@$(MAKE) $(AM_MAKEFLAGS) install-libLTLIBRARIES
	$(mkdir_p) $(top_srcdir)/$(BINARCHDIR)
if SYS_IS_CYGWIN
	cp $(libdir)/cvec.dll $(GAPINSTALLLIB)
else
	cp $(libdir)/cvec.so $(GAPINSTALLLIB)
endif
	@echo "SUCCESS!"

distclean-local:
	rm -rf bin/*
	(cd doc ; ./clean)

doc:	doc/manual.six

doc/manual.six: doc/cvec.xml doc/intro.xml doc/install.xml doc/datastrucs.xml \
		doc/vectors.xml doc/matrices.xml doc/performance.xml \
		doc/gaplib.xml doc/examples.xml doc/linalg.xml
	($(GAPROOT)/bin/gap.sh makedoc.g)

archive: doc
	(cd .. ; tar czvf cvec-`cat cvec/VERSION`.tar.gz --exclude ".svn" --exclude bin --exclude test --exclude ".git" --exclude ".libs" --exclude lib --exclude cvec.la --exclude cvec_la-cvec.lo --exclude .deps --exclude autom4te.cache --exclude .gitignore --exclude config.log --exclude stamp-h1 --exclude pkgconfig.h --exclude libtool --exclude config.status cvec)

WEBPOS=/scratch/neunhoef/mywebpage.pub/Computer/Software/Gap/cvec

towww: archive
	echo '<?xml version="1.0" encoding="ISO-8859-1"?>' >${WEBPOS}.version
	echo '<mixer>' >>${WEBPOS}.version
	cat VERSION >>${WEBPOS}.version
	echo '</mixer>' >>${WEBPOS}.version
	cp PackageInfo.g ${WEBPOS}
	cp README ${WEBPOS}/README.cvec
	cp doc/manual.pdf ${WEBPOS}/cvec.pdf
	cp ../cvec-`cat VERSION`.tar.gz ${WEBPOS}
	@echo
	@echo Now please adjust the archive link in 
	@echo "    " ${WEBPOS}.mixer !

