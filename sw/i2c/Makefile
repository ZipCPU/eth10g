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
all:	ddr3 edid sfp sird siclk temp si
I2CASM := ../host/i2casm
ZIPSW  := ../zipcpu/board

.PHONY: ddr3
## {{{
ddr3: $(ZIPSW)/ddr3.c
$(ZIPSW)/ddr3.c: $(I2CASM) ddr3.txt
	$(I2CASM) -c ddr3.txt -o $@
## }}}

.PHONY: edid
## {{{
edid: $(ZIPSW)/edid.c
$(ZIPSW)/edid.c: $(I2CASM) edid.txt
	$(I2CASM) -c edid.txt -o $@
## }}}

.PHONY: sfp
## {{{
sfp: $(ZIPSW)/sfp.c
$(ZIPSW)/sfp.c: $(I2CASM) sfp.txt
	$(I2CASM) -c sfp.txt -o $@
## }}}

.PHONY: sird
## {{{
sird: $(ZIPSW)/sird.c
$(ZIPSW)/sird.c: $(I2CASM) sird.txt
	$(I2CASM) -c sird.txt -o $@
## }}}

.PHONY: siclk
## {{{
siclk: $(ZIPSW)/siclk.c
$(ZIPSW)/siclk.c: $(I2CASM) siclk.txt
	$(I2CASM) -c siclk.txt -o $@
## }}}

.PHONY: si
## {{{
si: $(ZIPSW)/si.c
$(ZIPSW)/si.c: $(ZIPSW)/siclk.c $(ZIPSW)/sird.c
	cat $(ZIPSW)/siclk.c > $(ZIPSW)/si.c
	sed -e 's/i2casm/siconfig/' < $(ZIPSW)/siclk.c > $(ZIPSW)/si.c
	sed -e 's/i2casm/sird/' < $(ZIPSW)/sird.c >> $(ZIPSW)/si.c
## }}}

.PHONY: temp
## {{{
temp: $(ZIPSW)/temp.c
$(ZIPSW)/temp.c: $(I2CASM) temp.txt
	$(I2CASM) -c temp.txt -o $@
## }}}

.PHONY: clean
## {{{
clean:
	rm $(ZIPSW)/ddr3.c
	rm $(ZIPSW)/sfp.c
	rm $(ZIPSW)/edid.c
	rm $(ZIPSW)/siclk.c
	rm $(ZIPSW)/sird.c
	rm $(ZIPSW)/si.c
	rm $(ZIPSW)/temp.c
## }}}
