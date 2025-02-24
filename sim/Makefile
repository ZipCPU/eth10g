################################################################################
##
## Filename:	sim/Makefile
## {{{
## Project:	10Gb Ethernet switch
##
## Purpose:	To coordinate the build of a cycle accurate, Verilator based,
##		simulation of the main module.  Access to the simulation is
##	provided via the same software commands that will access the board, save
##	that the parameters are a touch different.  (See the access software for
##	more information ...)
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
.PHONY: all
# Make certain the "all" target is the first and therefore the default target
all:
CXX	:= g++
OBJDIR	:= obj-pc
RTLD	:= ../rtl
VOBJDR	:= $(RTLD)/obj_dir
VERILATOR_ROOT ?= $(shell bash -c 'verilator -V|grep VERILATOR_ROOT | head -1 | sed -e " s/^.*=\s*//"')
VROOT	:= $(VERILATOR_ROOT)
VVERSION:= ./vversion.sh
VDEFS   := $(shell $(VVERSION))
VINCD   := $(VROOT)/include
VINC	:= -I$(VINCD) -I$(VINCD)/vltstd -I$(VOBJDR)
INCS	:= -I. -I../sw/host -I$(RTLD) $(VINC)
GFXFLAGS:= `pkg-config gtkmm-3.0 --cflags`
GFXLIBS := `pkg-config gtkmm-3.0 --libs`
CFLAGS	:= -O3 -std=gnu++14 -faligned-new -Wall $(INCS) $(GFXFLAGS)
# CFLAGS	:= -Og -g -Wall $(INCS) -faligned-new
#
# A list of our sources and headers
#
##
## PROJECT sources for this project
SIMSOURCES:= flashsim.cpp sdspisim.cpp dbluartsim.cpp zipelf.cpp byteswap.cpp memsim.cpp hdmisim.cpp sdiosim.cpp
SIMOBJECTS:= $(addprefix $(OBJDIR)/,$(subst .cpp,.o,$(SIMSOURCES)))
# SIMHEADERS:= $(foreach header,$(subst .cpp,.h,$(SIMSOURCES)),$(wildcard $(header)))
VOBJS   := $(OBJDIR)/verilated.o $(OBJDIR)/verilated_vcd_c.o $(OBJDIR)/verilated_threads.o
SIMOBJ := $(subst .cpp,.o,$(SIMSOURCES))
SIMOBJS:= $(addprefix $(OBJDIR)/,$(SIMOBJ)) $(VOBJS)

SOURCES := $(SIMSOURCES) main_tb.cpp automaster_tb.cpp
HEADERS := $(foreach header,$(subst .cpp,.h,$(SOURCES)),$(wildcard $(header)))
#
PROGRAMS := main_tb
# Now the return to the "all" target, and fill in some details
all:	$(PROGRAMS)	sdcard.img emmc.img

$(OBJDIR)/%.o: %.cpp
	$(mk-objdir)
	$(CXX) $(CFLAGS) $(VDEFS) $(INCS) -c $< -o $@

$(OBJDIR)/%.o: $(VINCD)/%.cpp
	$(mk-objdir)
	$(CXX) $(CFLAGS) $(INCS) -c $< -o $@


MAINOBJS := $(OBJDIR)/main_tb.o $(OBJDIR)/automaster_tb.o
main_tb: $(MAINOBJS) $(SIMOBJECTS) $(VOBJS) $(VOBJDR)/Vmain__ALL.a
	$(CXX) $(CFLAGS) $^ $(VOBJDR)/Vmain__ALL.a -lelf $(GFXLIBS) -lpthread -o $@

# sdcard.img
## {{{
# Build a 64M SD-card image file that we can use for testing
sdcard.img:
	dd if=/dev/zero of=$@ bs=512 count=131072
	mkfs.fat $@
## }}}

#
# emmc.img
## {{{
# Build a 64M eMMC image file that we can use for testing
emmc.img:
	dd if=/dev/zero of=$@ bs=512 count=131072
	mkfs.fat $@
## }}}

#
# The "test" target, running hello world
#
.PHONY: test
test:
	./main_tb -d ../sw/zipcpu/board/hello

#
# The "clean" target, removing any and all remaining build products
# {{{
.PHONY: clean
clean:
	rm -f *.vcd
	rm -f $(PROGRAMS)
	rm -rf $(OBJDIR)/
## }}}

# mk-objdir: Build a directory to hold object files
## {{{
define	mk-objdir
	@bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR); fi"
endef
## }}}

# The "tags" target
# {{{
tags:	$(SOURCES) $(HEADERS)
	@echo "Generating tags"
	@ctags $(SOURCES) $(HEADERS)
## }}}

## Handle dependencies
## {{{
#
# The "depends" target, to know what files things depend upon.  The depends
# file itself is kept in $(OBJDIR)/depends.txt
#
define build-depends
	$(mk-objdir)
	@echo "Building dependency file"
	@$(CXX) $(CFLAGS) $(INCS) -MM $(SOURCES) > $(OBJDIR)/xdepends.txt
	@sed -e 's/^.*.o: /$(OBJDIR)\/&/' < $(OBJDIR)/xdepends.txt > $(OBJDIR)/depends.txt
	@rm $(OBJDIR)/xdepends.txt
endef

.PHONY: depends
depends: tags
	$(build-depends)

$(OBJDIR)/depends.txt: depends

ifneq ($(MAKECMDGOALS),clean)
-include $(OBJDIR)/depends.txt
endif
## }}}
