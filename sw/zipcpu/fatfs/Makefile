################################################################################
##
## Filename:	sw/zipcpu/fatfs/Makefile
## {{{
## Project:	10Gb Ethernet switch
##
## Purpose:	To guide/direct the build of a board-specific version of FatFS.
##
## Targets:	(all)
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2023-2025, Gisselquist Technology, LLC
## {{{
## This file is part of the ETH10G project.
##
## The ETH10G project contains free software and gateware, licensed under the
## terms of the 3rd version of the GNU General Public License as published by
## the Free Software Foundation.
##
## This project is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
## for more details.
##
## You should have received a copy of the GNU General Public License along
## with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
## target there if the PDF file isn't present.)  If not, see
## <http://www.gnu.org/licenses/> for a copy.
## }}}
## License:	GPL, v3, as defined and found on www.gnu.org,
## {{{
##		http://www.gnu.org/licenses/gpl.html
##
################################################################################
##
## }}}
CC := zip-gcc
AR := zip-ar
RDELF   := zip-readelf
OBJDUMP := zip-objdump
OBJDIR  := obj-zip
INCS    := -I. -I../../../rtl -I../zlib -I../board
CFLAGS  := -O3 $(INCS)
LIBSRCS := diskio.c ff.c ffsystem.c ffunicode.c sdspidrv.c sdiodrv.c emmcdrv.c
LIBOBJS := $(addprefix $(OBJDIR)/,$(subst .c,.o,$(LIBSRCS)))
FATLIB  := libfatfs.a
all: $(FATLIB)

$(OBJDIR)/%.o: %.c
	$(mk-objdir)
	$(CC) $(CFLAGS) -c $< -o $@

$(OBJDIR)/%.s: %.c
	$(mk-objdir)
	$(CC) $(CFLAGS) -fdump-rtl-all -S $< -o $@

$(OBJDIR)/%.txt: $(OBJDIR)/%.o
	bash -c "$(RDELF) -a $^ ; $(OBJDUMP) -S -D $^ " | tee -a $@


$(FATLIB): $(LIBOBJS)
	$(AR) -cru $@ $(LIBOBJS)

clean:
	rm -rf $(FATLIB) $(OBJDIR)/

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
