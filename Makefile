################################################################################
##
## Filename:	Makefile
## {{{
## Project:	10Gb Ethernet switch
##
## Purpose:	A master project makefile.  It tries to build all targets
##		within the project, mostly by directing subdirectory makes.
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
all:	check-install datestamp autodata sim sw test
#
# Defines and directories
## {{{
AUTOD := autodata
SIMD  := sim
#
# Could also depend upon load, if desired, but not necessary
BENCH := # `find bench -name Makefile` `find bench -name "*.cpp"` `find bench -name "*.h"`
SIM   := `find sim -name Makefile` `find sim -name "*.cpp"` `find sim -name "*.h"` `find sim -name "*.c"`
RTL   := `find rtl -name "*.v"` `find rtl -name Makefile`
NOTES := `find . -name "*.txt"` `find . -name "*.html"`
SW    := `find sw -name "*.cpp"` `find sw -name "*.c"`	\
	`find sw -name "*.h"`	`find sw -name "*.sh"`	\
	`find sw -name "*.py"`	`find sw -name "*.pl"`	\
	`find sw -name "*.png"`	`find sw -name Makefile`
DEVSW := `find sw/board -name "*.cpp"` `find sw/board -name "*.h"` \
	`find sw/board -name Makefile`
PROJ  :=
BIN  := # `find xilinx -name "*.bit"`
AUTODATA := `find $(AUTOD) -name "*.txt"` `find $(AUTOD) -name Makefile`
CONSTRAINTS := `find . -name "*.xdc"`
YYMMDD:=`date +%Y%m%d`
SUBMAKE:= $(MAKE) --no-print-directory -C
LOADER:= openFPGALoader
## }}}
##
## Check that we have all the programs available to us that we need
## {{{
#
.PHONY: check-install
check-install: check-perl check-autofpga check-verilator check-zip-gcc check-gpp check-loader

.PHONY: check-perl
	$(call checkif-installed,perl,)

.PHONY: check-autofpga
check-autofpga:
	$(call checkif-installed,autofpga,-V)

.PHONY: check-verilator
check-verilator:
	$(call checkif-installed,verilator,-V)

.PHONY: check-zip-gcc
check-zip-gcc:
	$(call checkif-installed,zip-gcc,-v)

.PHONY: check-gpp
check-gpp:
	$(call checkif-installed,g++,-v)

.PHONY: check-loader
check-loader:
	$(call checkif-installed,openFPGALoader,-V)

## }}}
#
#
# Now that we know that all of our required components exist, we can build
# things
#
#
.PHONY: datestamp
## {{{
# Create a datestamp file, so that we can check for the build-date when the
# project was put together.
#
datestamp: check-perl
	@bash -c 'if [ ! -e $(YYMMDD)-build.v ]; then rm -f 20??????-build.v; perl mkdatev.pl > $(YYMMDD)-build.v; rm -f rtl/builddate.v; fi'
	@bash -c 'if [ ! -e rtl/builddate.v ]; then cd rtl; cp ../$(YYMMDD)-build.v builddate.v; fi'
## }}}

.PHONY: archive
## {{{
#
## Make a tar archive of this file, as a poor man's version of source code
## control. (Sorry ... I've been burned too many times by files I've wiped
## away ...)
#
ARCHIVEFILES := $(BENCH) $(SW) $(RTL) $(SIM) $(NOTES) $(PROJ) $(BIN) $(CONSTRAINTS) $(AUTODATA) README.md
archive:
	tar --transform s,^,$(YYMMDD)-tii/, --exclude=dump.txt --exclude=trace.vcd -chjf $(YYMMDD)-eth10g.tjz $(ARCHIVEFILES)

## }}}
################################################################################
##
## Auto-FPGA
## {{{
.PHONY: autodata
## Build our main (and toplevel) Verilog files via autofpga
##
autodata: check-autofpga
	$(SUBMAKE) $(AUTOD)
	$(call copyif-changed,$(AUTOD)/toplevel.v,rtl/toplevel.v)
	$(call copyif-changed,$(AUTOD)/main.v,rtl/main.v)
	$(call copyif-changed,$(AUTOD)/iscachable.v,rtl/cpu/iscachable.v)
	$(call copyif-changed,$(AUTOD)/build.xdc,rtl/board.xdc)
	$(call copyif-changed,$(AUTOD)/regdefs.h,sw/host/regdefs.h)
	$(call copyif-changed,$(AUTOD)/regdefs.cpp,sw/host/regdefs.cpp)
	$(call copyif-changed,$(AUTOD)/board.h,sw/zipcpu/zlib/board.h)
	$(call copyif-changed,$(AUTOD)/board.h,sw/zipcpu/board/board.h)
	$(call copyif-changed,$(AUTOD)/bkram.ld,sw/zipcpu/board/bkram.ld)
	$(call copyif-changed,$(AUTOD)/bkram.ld,sw/zipcpu/board/board.ld)
	$(call copyif-changed,$(AUTOD)/rtl.make.inc,rtl/make.inc)
	$(call copyif-changed,$(AUTOD)/testb.h,$(SIMD)/testb.h)
	$(call copyif-changed,$(AUTOD)/main_tb.cpp,$(SIMD)/main_tb.cpp)

# $(call copyif-changed,$(AUTOD)/sdram.ld,sw/zipcpu/board/sdram.ld)
# $(call copyif-changed,$(AUTOD)/board.ld,sw/boot/board.ld)
# $(call copyif-changed,$(AUTOD)/bootrom.ld,sw/zipcpu/boot/bootrom.ld)
# $(call copyif-changed,$(AUTOD)/bootrom.ld,sw/zipcpu/board/bootrom.ld)
## }}}
################################################################################
##
## RTL: Lint RTL, Verilate, build bit file, etc.
## {{{
.PHONY: verilated rtl
#
# Verify that the rtl has no bugs in it, while also creating a Verilator
# simulation class library that we can then use for simulation
#
verilated: datestamp check-verilator
	+@$(SUBMAKE) rtl

.PHONY: rtl
rtl: verilated

## }}}
################################################################################
##
## Simulation target
## {{{
## Build a simulation of this entire design
## (Running it will be part of the test target below)
##
.PHONY: sim
sim: rtl check-gpp
	+@$(SUBMAKE) $(SIMD)
## }}}
################################################################################
##
## Software targets
## {{{
##
## A master target to build all of the support software
##
.PHONY: sw
sw: sw-host sw-zlib sw-fatfs sw-board # sw-boot

.PHONY: sw-host host
## {{{
##
## Build the host support software
##
host: sw-host
sw-host: check-gpp
	+@$(SUBMAKE) sw/host
## }}}

.PHONY: sw-i2c
## {{{
##
## Build the data for the I2C files
##
sw-i2c: sw-host
	+@$(SUBMAKE) sw/i2c
## }}}

.PHONY: sw-zlib zlib
## {{{
zlib: sw-zlib
##
## Build the hardware specific newlib library
##
sw-zlib: check-zip-gcc
	+@$(SUBMAKE) sw/zipcpu/zlib
## }}}

.PHONY: sw-fatfs fatfs
## {{{
fatfs: sw-fatfs
##
## Build the hardware specific newlib library
##
sw-fatfs: check-zip-gcc
	+@$(SUBMAKE) sw/zipcpu/fatfs
## }}}

.PHONY: sw-board sw-zipcpu sw-fatfs
## {{{
## Build the board software.  This may (or may not) use the software library
##
sw-zipcpu: sw-board
sw-board: sw-i2c sw-zlib sw-fatfs check-zip-gcc
	+@$(SUBMAKE) sw/zipcpu/board
## }}}

# .PHONY: sw-boot
## {{{
##
## Build the boot software.
##
# sw-boot: check-zip-gcc sw-zlib
#	+@$(SUBMAKE) sw/boot
## }}}
## }}}
################################################################################
##
## Test targets
## {{{
.PHONY: test formal

#
# Run "Hello World", and ... see if this all works
#
#.PHONY: hello
#hello: sim sw
#	$(SIMD)/main_tb sw/board/hello

# .PHONY: sdtest
# sdtest: sim sw
#	$(SIMD)/main_tb sw/board/sdtest

#test: hello

formal:
	$(SUBMAKE) bench/formal

vtest:	sim
	$(SUBMAKE) sim test

test: formal vtest
## }}}
################################################################################
##
## Load the device
## {{{
BITFILE := toplevel.bit
$(BITFILE): ../xilinx/eth10g.runs/impl_1/toplevel.bit
	@cp $< $@

.PHONY: load
load: $(BITFILE)
	$(LOADER) -c digilent $(BITFILE)
## }}}
################################################################################
##
## Macro definitions
## {{{

# copyif-changed
## {{{
##
## Copy a file from the auto-data directory that had been created by
## autofpga, into the directory structure where it might be used.
##
define	copyif-changed
	@bash -c 'cmp $(1) $(2); if [[ $$? != 0 ]]; then echo "Copying $(1) to $(2)"; cp $(1) $(2); fi'
endef
## }}}

# checkif-installed
## {{{
##
## Check if the given program is installed
##
define	checkif-installed
	@bash -c '$(1) $(2) < /dev/null >& /dev/null; if [[ $$? != 0 ]]; then echo "Program not found: $(1)"; exit -1; fi'
endef
## }}}
## }}}
################################################################################
##
.PHONY: clean
## {{{
clean:
	+$(SUBMAKE) $(AUTOD)	clean
	+$(SUBMAKE) $(SIMD)	clean
	+$(SUBMAKE) rtl		clean
	+$(SUBMAKE) sw/zipcpu/zlib	clean
	+$(SUBMAKE) sw/zipcpu/board	clean
	+$(SUBMAKE) sw/host	clean
## }}}
