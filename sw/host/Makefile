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
.PHONY: all
all:
## }}}
## Defines and directories
## {{{
CXX := g++
OBJDIR := obj-pc
SCOPES := smiscope flashscope fanscope cfgscope i2cscope
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

netuart: $(OBJDIR)/netuart.o
	$(CXX) $(CFLAGS) $^ -o $@

wbregs: $(OBJDIR)/wbregs.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@

cfgscope: $(OBJDIR)/cfgscope.o $(OBJDIR)/scopecls.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@

fanscope: $(OBJDIR)/fanscope.o $(OBJDIR)/scopecls.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@

i2cscope: $(OBJDIR)/i2cscope.o $(OBJDIR)/scopecls.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@

flashscope: $(OBJDIR)/flashscope.o $(OBJDIR)/scopecls.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@

smiscope: $(OBJDIR)/smiscope.o $(OBJDIR)/scopecls.o $(BUSOBJS)
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
