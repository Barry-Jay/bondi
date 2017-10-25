##########################################################################
# 
# Bondi Makefile.in
# Copyright (c) 2008, Barry Jay 
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are
# met:
#
#    * Redistributions of source code must retain the above copyright
#    * notice, this list of conditions and the following disclaimer.
#
#    * Redistributions in binary form must reproduce the above
#    * copyright notice, this list of conditions and the following
#    * disclaimer in the documentation and/or other materials provided
#    * with the distribution.
#
#    * Neither the name of Barry Jay nor bondi nor the names of its
#    * contributors may be used to endorse or promote products derived
#    * from this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
# A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
# OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
# SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
# LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
# DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
# THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
# 
# Contributors:
#     Arun Kumar (arun@it.uts.edu.au)
#
###############################################################################

# Set `dep' to a non-empty value if you want dependencies regenerated
# whenever a source file changes (slow!)
dep = 

# Set `verbose' to a non-empty value if you want many nonessential
# informative files to be created (e.g. the *.interface files)
verbose = t


#### Programs and their options ####
INCLUDE     = -I /usr/local/lib/ocaml
DEBUG       = -g
OCAMLCFLAGS = -unsafe
OCAMLI      = ocamlc -c
OCAMLC      = ocamlc $(DEBUG) -I ./config/byte
OCAMLOPT    = no -inline 1 -I ./config/native -thread
OCAMLDEP    = ocamldep
OCAMLLEX    = ocamllex
OCAMLYACC   = ocamlyacc $(if $(verbose),-v,)
OCAMLDOT    = no
CC     = gcc
CFLAGS = -DHAVE_GNU_READLINE -O2 $(DEBUG) -Wall -ansi -pedantic -W -Wwrite-strings
LD     = ld
LFLAGS = -lc
AS     = as
AR     = ar
RANLIB = ranlib
CDEP   = gcc -MM
CPP    = gcc -E -E
PERL   = perl -w
OCAML_LIBRARY = $(l_readline)
PREFIX  =/usr
DESTDIR =
BONDILIB =/usr/lib/bondi
MODEL  = unknown
SYSTEM = linux-gnu
ARCH   = x86_64
#### End of configuration section ####

# Default rule
all:

# We don't use any built-in rule
.SUFFIXES:


# Configuration
-include config/native/config.make          

config/byte config/byte/config.ml config/native config/native/config.ml:
	$(MAKE) -C config config
config/%/config.cmi: config.cmi
	cp -p $< $@

.PHONY: config
config:
	$(MAKE) -C config config

# Just mention these in a rule so that they don't get deleted if they
# are intermediate targets.
$(foreach dir,byte native,$(foreach ext,make mli ml cmi cmo cmx o,config/$(dir)/config.$(ext))):



# Some common variables
files_ml = $(wildcard *.ml)
generated_ml_files = \
        $(patsubst %l,%,$(wildcard *.mll)) \
        $(patsubst %y,%,$(wildcard *.mly)) \
        bondi.ml
generated_mli_files = \
        $(patsubst %y,%i,$(wildcard *.mly))
modules_ml = $(generated_ml_files) $(files_ml)
# byte_modules and native_modules are defined from .depend --- see below

# Include .depend now since it contains variable definitions
ifneq ($(wildcard .depend),)
include .depend
endif

# $(byte_modules) is defined in .depend. We need two slightly
# different variables for bytecode and native compilation.
byte_modules = $(native_modules:./config/native/%=./config/byte/%)


# help lists the most useful rules
.PHONY: help
help::
	@echo 'help            Display this text.'


# Makefile debugging
.PHONY: echo
help::
	@echo 'echo variable=FOO   print $$(FOO)'
echo:
	@echo $($(variable))


# Miscellaneous cleanup rules
.PHONY: dust clean clobber dist-clean neat
help::
	@echo 'clean           Remove most generated files.'
	@echo 'clobber         Remove all generated files.'
	@echo 'dust            Remove ``useless'\'\'' files, e.g., backup files.'
	@echo 'neat            Remove all but user-written files.'
	@echo 'dist-clean      Remove all but user-written files and some platform-'; \
	echo '                independant generated files'
neat:: dust clobber
dist-clean:: dust
dust::
	-rm -f *~ \#*\# core
clean::
	-rm -f parse.ml parse.mli lex.ml
	-rm -f *.cmi *.cmo *.cmx *.cmxa *.o *.a *.output *.log *.status .depend
	-rm -f config/native/*.cmx config/native/*.cmi 
clobber dist-clean:: clean
	-rm -f $(generated_ml_files) $(generated_mli_files) *.interface *.frz
dust clean clobber dist-clean neat::
	$(MAKE) -C config $@




# Most common rules
.PHONY: native byte prof all
all: native 
# standard_prelude.frz
help::
	@echo 'all             Build the Bondi compiler and `out_bondi'\'', in bytecode.'
byte: bondi.byte
help::
	@echo 'bondi.byte       Build the Bondi compiler, in bytecode.'
prof: bondi.prof
help::
	@echo 'bondi.prof       Build the Bondi compiler, instrumented for profiling.'
native: system bondi message
help::
	@echo 'bondi            Build the Bondi compiler, in native code.'

.PHONY: bondi.native bondi.opt
bondi.opt bondi.native:
	@echo 'Building the Bondi compiler in native code as `bondi'\'
	+$(MAKE) bondi


# End products
out_bondi: out_bondi.o
	rm -f $@
	$(LD) $(LFLAGS) -o $@ out_bondi.o -L. -lbondi
bondi: $(readline_o) $(native_modules:%=%.cmx) $(native_modules:%=%.o)
	$(OCAMLOPT) $(ODBCINCLUDE) $(OCAMLCFLAGS) -o $@ $(unix_o) $(threads_o) $(ODML) $(native_modules:%=%.cmx) $(readline_o) -cclib "$(LFLAGS)" $(OCAML_LIBRARY) $(l_unix) -cclib -lcurses
	-mv $@ ../
bondi.byte: gnu_readline.o $(byte_modules:%=%.cmo)
	rm -f $@
	$(OCAMLC) $(OCAMLCFLAGS) -o $@ $(byte_modules:%=%.cmo)
# bondi.prof: # TODO
clobber dist-clean::
	-rm -f bondi.byte bondi.prof out_bondi bondi

bondi.ml: .depend
	rm -f $@
	for m in $(byte_modules); do \
          echo "#load \"$$m.cmo\";;"; \
        done >$@

clobber dist-clean::
	-rm -f bondi.dot bondi_dependency_diagram.ps
bondi.dot: $(byte_modules:%=%.ml)
	$(OCAMLDOT) $^ >$@

install-tests:
	-../scripts/install-tests.sh -d "tests pc_book lib xml"

# Testing
.PHONY: test tests check checks
help::
	@echo 'test            Run some tests of the compiler.'
test tests check checks: install-checks
	$(MAKE) -s -C ../tests check
	$(MAKE) -s -C ../pc_book check
	$(MAKE) -s -C ../lib check
	$(MAKE) -s -C ../xml check


# Distribution
.PHONY: distrib
help::
	@echo 'distrib         Make an archive containing the user-written files.'
archive ?= ../bondi2-current.tar.gz
archive_contents = $(filter-out CVS tmp Do_not_distribute $(shell test -r Do_not_distribute && cat <Do_not_distribute) $(foreach shell_pattern,$(filter-out $(archive) rm -f,$(shell $(MAKE) -n dist-clean)),$(wildcard $(shell_pattern))),$(wildcard *)) # aargh!
distrib:
	rm -f $(archive)
	files='$(archive_contents)'; tar cf - $$files | gzip -9 >'$(archive)'

.PHONY: install uninstall

install: 
	./install-sh -d $(DESTDIR)$(PREFIX)/bin          
	./install-sh -d $(DESTDIR)$(PREFIX)/lib/bondi
	./install-sh -c ../bondi $(DESTDIR)$(PREFIX)/bin
	./install-sh ../prelude $(DESTDIR)$(PREFIX)/lib/bondi
	./install-sh ../lib     $(DESTDIR)$(PREFIX)/lib/bondi
	./install-sh ../pc_book $(DESTDIR)$(PREFIX)/lib/bondi
	./install-sh ../xml     $(DESTDIR)$(PREFIX)/lib/bondi
	./install-sh ../samples $(DESTDIR)$(PREFIX)/lib/bondi
	./install-sh ../containers $(DESTDIR)$(PREFIX)/lib/bondi

uninstall:
	-rm $(DESTDIR)$(PREFIX)/bin/bondi
	-rm -rf $(DESTDIR)$(PREFIX)/lib/bondi

system: 
	@rm -f system.ml
	sed -e 's|%%LIBDIR%%|$(PREFIX)/lib/bondi|' \
            -e 's|%%ARCH%%|$(ARCH)|' \
            -e 's|%%MODEL%%|$(MODEL)|' \
            -e 's|%%SYSTEM%%|$(SYSTEM)|' \
            system.mlp > system.ml
	@chmod -w system.ml

message:
	@echo "    -----------------------------------------------------"
	@echo "               Bondi build complete"
	@echo ""
	@echo "     Bondi Environment Variables:"
	@echo "         BONDI_LIB_DIR: $(BONDILIB)"
	@echo ""
	@echo "     Bondi will install into the following directories:"
	@echo "         BIN: $(PREFIX)/bin"
	@echo "         LIB: $(BONDILIB)"
	@echo ""
	@echo "     To install Bondi:"
	@echo "     1. ensure you have root privileges"
	@echo "     2. cd src"
	@echo "     3. make install"
	@echo "     4. cd ../"
	@echo ""
	@echo "     *INSTALLATION WILL OVERWRITE EXISTING BONDI INSTALL*" 
	@echo "    -----------------------------------------------------"

# Generic preprocessing and compilation rules
%.ml: %.mll
	$(OCAMLLEX) $<
%.ml %.mli $(if $(verbose),%.output,): %.mly
	$(OCAMLYACC) $<
%.cmi: %.mli
	$(OCAMLI) $(INCLUDE) $<
%.cmo $(if $(verbose),%.interface,): %.ml %.cmi
	$(OCAMLC) $(INCLUDE) $(OCAMLCFLAGS)  -c $< 
%.cmx %.o $(if $(verbose),%.interface,): %.ml %.cmi
	$(OCAMLOPT) $(INCLUDE) $(OCAMLCFLAGS)  -c $< 
%.o: %.c
	$(CC) $(CFLAGS) $(INCLUDE) -c $<

%.frz: %.fsh
	$(MAKE) bondi
	@echo ./bondi -f -e
	@( $(foreach d,$(filter %.frz,$^),echo '%thaw "$d";;';) \
           echo '%use "$<";;'; \
           echo '%freeze "$@";;' ) | ./bondi -f -e

# Just mention these in a rule so that they don't get deleted if they
# are intermediate targets.
$(generated_mli_files) $(generated_ml_files):
# standard_prelude.frz:



# dependencies
.PHONY: dep depend
help::
	@echo 'dep             (Re)generate the list of dependencies (.depend).'; \
         echo '               ** You need to do this before actually trying to build **'; \
         echo '               ** anything.                                           **'
clobber dist-clean::
	-rm -f .depend
dep depend: system
	rm -f .previous.depend BAD.depend
	-mv .depend .previous.depend 2>/dev/null
	@if $(MAKE) dep=t .depend; then \
                rm -f .previous.depend; \
        else \
                rm -f BAD.depend; \
                mv -f .depend BAD.depend; \
                echo 'The incorrect `.depend'\'' was moved to `BAD.depend'\''.'; \
        fi

dust::
	-rm -f BAD.depend
clean dust::
	-rm -f config.ml
ifeq ($(dep),)
.depend: ;
else
# The dep variable trick is good but not perfect.
# Bug: I remove bondi.ml here; this is incorrect, but it doesn't really
# matter.
.depend: $(generated_mli_files) $(filter-out bondi.ml,$(generated_ml_files)) \
	config/byte/config.ml config/native/config.ml
	rm -f .depend bondi.ml
	@echo '# Automatically generated dependencies -- do not edit' >>.depend
	$(OCAMLDEP) -I ./config/byte *.mli *.ml >>.depend
	( echo '1,$$s!byte/config\.cmx!native/config.cmx!'; \
          echo w; echo q ) \
          | ed .depend
	$(OCAMLDEP) config/*/config.ml >>.depend
	$(CDEP) $(INCLUDE) *.c >>.depend
	./reorder-cmx --prepend='native_modules = ' shell <.depend >>.depend
endif


# End of file `GNUmakefile'.
