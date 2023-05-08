################################################################################
##
## Filename:	Makefile
## {{{
## Project:	10Gb Ethernet switch
##
## Purpose:	To guide/direct the build of the board-specific portion of
##		newlib.
##
## Targets:	
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2023, Gisselquist Technology, LLC
## {{{
## This file is part of the ETH10G project.
##
## The ETH10G project contains free software and gateware, licensed under the
## Apache License, Version 2.0 (the "License").  You may not use this project,
## or this file, except in compliance with the License.  You may obtain a copy
## of the License at
## }}}
##	http://www.apache.org/licenses/LICENSE-2.0
## {{{
## Unless required by applicable law or agreed to in writing, files
## distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
## WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
## License for the specific language governing permissions and limitations
## under the License.
##
################################################################################
##
## }}}
CC := zip-gcc
AR := zip-ar
OBJDIR  := obj-zip
INCS    := -I. -I../../../rtl
CFLAGS  := -O3 $(INCS)
LIBSRCS := udiv.c umod.c syscalls.c crt0.c
LIBOBJS := $(addprefix $(OBJDIR)/,$(subst .c,.o,$(LIBSRCS)))
ZIPLIB  := libzeth.a
all: $(ZIPLIB)

$(OBJDIR)/%.o: %.c
	$(mk-objdir)
	$(CC) $(CFLAGS) -c $< -o $@

$(OBJDIR)/%.s: %.c
	$(mk-objdir)
	$(CC) $(CFLAGS) -fdump-rtl-all -S $< -o $@

$(OBJDIR)/crt0.o: crt0.c
	$(mk-objdir)
	$(CC) $(CFLAGS) -ffreestanding -c $< -o $@

$(ZIPLIB): $(LIBOBJS)
	$(AR) -cru $@ $(LIBOBJS)

clean:
	rm -rf $(ZIPLIB) $(OBJDIR)/

define	mk-objdir
	@bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR); fi"
endef

define	build-depends
	@echo "Building dependency file(s)"
	$(mk-objdir)
	@$(CC) $(CFLAGS) -MM $(LIBSRCS) > $(OBJDIR)/xdepends.txt
	@sed -e 's/^.*.o: /$(OBJDIR)\/&/' < $(OBJDIR)/xdepends.txt > $(OBJDIR)/depends.txt
	@rm $(OBJDIR)/xdepends.txt
endef

tags: $(LIBSRCS) $(HEADERS)
	@echo "Generating tags"
	@ctags $(LIBSRCS) $(HEADERS)


.PHONY: depends
depends: tags
	$(build-depends)

$(OBJDIR)/depends.txt: $(SOURCES) $(HEADERS)
	$(build-depends)

-include $(OBJDIR)/depends.txt
