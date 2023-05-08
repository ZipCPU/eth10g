################################################################################
##
## Filename:	Makefile
## {{{
## Project:	10Gb Ethernet switch
##
## Purpose:	
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
.PHONY: all
PROGRAMS := hello cputest # contest sdtest gpiotoggle dmatest
all:	$(PROGRAMS)
#
#
CC	:=zip-gcc
AS	:=zip-as
LD	:=zip-ld
NM	:=zip-nm
OBJDIR	:= obj-zip
RDELF	:= zip-readelf
OBJDUMP := zip-objdump
SUBMAKE:= $(MAKE) --no-print-directory -C
#
#
TTTT    := tttt
SOURCES := hello.c sdtest.c cputest.c gpiotoggle.c contest.c	\
		clkgatechk.c dmatest.c # rintftst.c
HEADERS :=
DUMPRTL := -fdump-rtl-all
DUMPTREE:= -fdump-tree-all
LDSCRIPT:= board.ld
LFLAGS  := -T $(LDSCRIPT) -L../zlib
LBKRAM  := -T bkram.ld -L../zlib
CFLAGS  := -O3 -I../zlib -I../../../rtl
LIBS    := -lc -lzeth -lgcc
INSTALLD=$(shell bash -c "which zip-gcc | sed -e 's/.cross-tools.*$\//'")
NLIBD=$(INSTALLD)/cross-tools/zip/lib
ZLIBD=../zlib
LIB=$(ZLIBD)/libzeth.a $(NLIBD)/libg.a $(NLIBD)/libc.a
#
# For source analysis, the following macros are defined:
#

%.o: $(OBJDIR)/%.o
$(OBJDIR)/%.o: %.c
	$(mk-objdir)
	$(CC) $(CFLAGS) -c $< -o $@
$(OBJDIR)/%.s: %.c
	$(mk-objdir)
	$(CC) $(CFLAGS) $(DUMPRTL) -S $< -o $@
$(OBJDIR)/%.txt: $(OBJDIR)/%.o
	bash -c "$(RDELF) -a $^ ; $(OBJDUMP) -S -D $^ " | tee -a $@
%.txt: %
	$(OBJDUMP) -S -D $^ > $@


#
# The CPUTest program here is special--it doesn't use the C library.  Hence,
# it must have the -fno-builtin flag in order to build, and the -Tartyram.ld
# linker script to build something that doesn't go into flash but directly into
# RAM instead.
#
$(OBJDIR)/cputest.o: cputest.c
	$(mk-objdir)
	$(CC) $(CFLAGS) -c -Wa,-nocis -fno-builtin $< -o $@
$(OBJDIR)/cputestcis.o: cputest.c
	$(mk-objdir)
	$(CC) $(CFLAGS) -c -Wa,-cis -fno-builtin $< -o $@
$(OBJDIR)/cputest.s: cputest.c
	$(CC) $(CFLAGS) -S -Wa,-cis -fno-builtin $< -o $@

cputest: $(OBJDIR)/cputestcis.o board.ld $(LIB)
	# $(CC) $(CFLAGS) $(LFLAGS) $< $(LIBS) -o $@
	$(CC) $(CFLAGS) $(LBKRAM) $< $(LIBS) -o $@


$(OBJDIR)/contest.o: contest.c
	$(mk-objdir)
	$(CC) $(CFLAGS) -c -fno-builtin $< -o $@

contest: $(OBJDIR)/contest.o $(OBJDIR)/txfns.o board.ld $(LIB)
	$(CC) $(CFLAGS) $(LFLAGS) $< $(OBJDIR)/txfns.o $(LIBS) -o $@

$(OBJDIR)/hello.o: hello.c
	$(CC) -O3 -c $< -o $@
$(OBJDIR)/rintftst.o: rintftst.c
	$(CC) $(CFLAGS) -O3 -c $< -o $@
$(OBJDIR)/gpiotoggle.o: gpiotoggle.c
#	$(CC) -O3 -c $< -o $@

hello: $(OBJDIR)/hello.o board.ld $(LIB)
	$(CC) $(CFLAGS) $(LFLAGS) $< $(LIBS) -o $@

rintftst: $(OBJDIR)/rintftst.o $(OBJDIR)/txfns.o board.ld $(LIB)
	$(CC) $(CFLAGS) $(LFLAGS) $< $(OBJDIR)/txfns.o $(LIBS) -o $@

sdtest: $(OBJDIR)/sdtest.o board.ld $(LIB)
	$(CC) $(CFLAGS) $(LFLAGS) $< $(LIBS) -o $@

gpiotoggle: $(OBJDIR)/gpiotoggle.o bkram.ld $(LIB)
	$(CC) $(CFLAGS) $(LFLAGS) $< $(LIBS) -o $@

hellostep: $(OBJDIR)/hellostep.o bkram.ld $(OBJDIR)/txfns.o $(LIB)
	$(CC) $(CFLAGS) $(LFLAGS) $< $(OBJDIR)/txfns.o $(LIBS) -o $@

lockcheck: $(OBJDIR)/lockcheck.o $(OBJDIR)/txfns.o bkram.ld $(LIB)
	$(CC) $(CFLAGS) $(LFLAGS) $< $(OBJDIR)/txfns.o $(LIBS) -o $@

dmatest: $(OBJDIR)/dmatest.o $(OBJDIR)/txfns.o bkram.ld $(LIB)
	$(CC) $(CFLAGS) $(LFLAGS) $< $(LIBS) -o $@

clkgatechk: $(OBJDIR)/clkgatechk.o $(OBJDIR)/txfns.o bkram.ld $(LIB)
	$(CC) $(CFLAGS) $(LFLAGS) $< $(OBJDIR)/txfns.o $(LIBS) -o $@

.PHONY: iftttt
ifeq (,$(wildcard tttt/))
iftttt:
else
iftttt: 
	$(SUBMAKE) tttt/src ARCH=zip CROSS=zip- zip-tttt
endif

.PHONY: tttt
tttt:
	@bash -c "if [ ! -e $(TTTT)/src/Makefile ]; then git submodule add https://github.com/ZipCPU/tttt; git submodule init; git submodule update; fi"
	CROSS=zip- ARCH=zip $(SUBMAKE) tttt/src ARCH=zip CROSS=zip- zip-tttt


hellosim: hellosim.s
	$(AS) $< -o $(OBJDIR)/hellosim.o
	$(LD) -T bkram.ld $(OBJDIR)/hellosim.o -o $@


define	mk-objdir
	@bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR)/; fi"
endef

define	build-depends
	@echo "Building dependency file(s)"
	$(mk-objdir)
	@$(CC) $(CFLAGS) -MM $(SOURCES) > $(OBJDIR)/xdepends.txt
	@sed -e 's/^.*.o: /$(OBJDIR)\/&/' < $(OBJDIR)/xdepends.txt > $(OBJDIR)/depends.txt
	@rm $(OBJDIR)/xdepends.txt
endef

tags: $(SOURCES) $(HEADERS)
	@echo "Generating tags"
	@ctags $(SOURCES) $(HEADERS)

.PHONY: depends
depends: tags
	$(build-depends)

$(OBJDIR)/depends.txt: $(SOURCES) $(HEADERS)
	$(build-depends)

.PHONY: clean
clean:
	rm -f $(PROGRAMS) hellosim
	rm -rf $(addsuffix .map,$(PROGRAMS))
	rm -rf $(addsuffix .txt,$(PROGRAMS))
	rm -rf $(OBJDIR)/
ifneq (,$(wildcard tttt/))
	$(SUBMAKE) tttt/src ARCH=zip CROSS=zip- clean
endif

ifneq ($(MAKECMDGOALS),clean)
-include $(OBJDIR)/depends.txt
endif
