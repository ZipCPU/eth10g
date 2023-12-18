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
