################################################################################
##
## Filename:	sw/host/Makefile
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
.PHONY: all
all:
## }}}
## Defines and directories
## {{{
CXX := g++
OBJDIR := obj-pc
SCOPES := smiscope flashscope fanscope cfgscope i2cscope sdioscope emmcscope netscope rxedidscope cpunetscope routescope
RTLD := ../../rtl
ZIPSUPPORT := zipload zipstate zipdbg
BUSSRCS := ttybus.cpp llcomms.cpp regdefs.cpp byteswap.cpp devbus.cpp
BUSOBJS := $(addprefix $(OBJDIR)/,$(subst .cpp,.o,$(BUSSRCS)))
PROGRAMS := wbregs $(ZIPSUPPORT) $(SCOPES) flashid netuart
SOURCES := $(addsuffix .cpp,$(PROGRAMS)) $(BUSSRCS)
HEADERS := $(wildcard *.h) $(wildcard $(RTLD)/*.h)
CFLAGS := -Og -g -Wall -I. -I$(RTLD)
LIBS :=
## }}}
all: $(PROGRAMS)

## Default build target formulas
## {{{
%.o: $(OBJDIR)/%.o
$(OBJDIR)/%.o: %.cpp
	$(mk-objdir)
	$(CXX) $(CFLAGS) -c $< -o $@
## }}}

%scope: $(OBJDIR)/%scope.o $(OBJDIR)/scopecls.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@

netuart: $(OBJDIR)/netuart.o
	$(CXX) $(CFLAGS) $^ -o $@

wbregs: $(OBJDIR)/wbregs.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@

zipdbg: $(OBJDIR)/zipdbg.o $(OBJDIR)/twoc.o $(OBJDIR)/zopcodes.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -lncurses -o $@

zipload: $(OBJDIR)/zipload.o $(OBJDIR)/flashdrvr.o $(OBJDIR)/zipelf.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -lelf -o $@

zipstate: $(OBJDIR)/zipstate.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@

flashid: $(OBJDIR)/flashid.o $(OBJDIR)/flashdrvr.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@

################################################################################
##
## Macro definitions
## {{{

# mk-objdir
## {{{
##
## Creates a directory for object files if it doesn't exist already
##
define	mk-objdir
	@bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR); fi"
endef
## }}}

# build-depends
## {{{
define build-depends
	@echo "Building dependency file(s)"
	$(mk-objdir)
	@$(CXX) $(CFLAGS) -MM $(SOURCES) > $(OBJDIR)/xdepends.txt
	@sed -e 's/^.*.o: /$(OBJDIR)\/&/' < $(OBJDIR)/xdepends.txt > $(OBJDIR)/depends.txt
	@rm $(OBJDIR)/xdepends.txt
endef
## }}}
## }}}
##
.PHONY: clean
## {{{
clean:
	rm -rf $(OBJDIR)/ $(PROGRAMS)
## }}}
################################################################################
##
## Dependency handling
## {{{
tags: $(SOURCES) $(HEADERS)
	@echo "Generating tags"
	@ctags $(SOURCES) $(HEADERS)

.PHONY: depends
depends: tags
	$(build-depends)

$(OBJDIR)/depends.txt: $(SOURCES) $(HEADERS)
	$(build-depends)

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),depends)
-include $(OBJDIR)/depends.txt
endif
endif
## }}}
