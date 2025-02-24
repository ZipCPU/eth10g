################################################################################
##
## Filename:	doc/Makefile
## {{{
## Project:	10Gb Ethernet switch
##
## Purpose:	To coordinate the build of documentation PDFs from their
##		LaTeX sources.
##
##	Targets include:
##		all		Builds all documents
##
##		axin
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
all:	axin
pdf:	axin
DSRC := src

.PHONY: axin
axin: axin.pdf
## {{{
axin.pdf: $(DSRC)/axin.tex $(DSRC)/title2023.tex
axin.pdf: $(DSRC)/fvcharts.sty $(DSRC)/powerdot-gt.sty
axin.pdf: $(DSRC)/zverilog.sty $(DSRC)/zvhdl.sty
	cd $(DSRC)/; latex axin.tex
	cd $(DSRC)/; latex axin.tex
	cd $(DSRC)/; dvips -z -P pdf axin.dvi -o ../axin.ps
	ps2pdf axin.ps
	@rm -f $(DSRC)/axin.dvi $(DSRC)/axin.log
	@rm -f $(DSRC)/axin.aux $(DSRC)/axin.toc
	@rm -f $(DSRC)/axin.lot $(DSRC)/axin.lof
	@rm -f $(DSRC)/axin.out $(DSRC)/axin.bm
	@rm -f $(DSRC)/axin.vrb
	@rm -f axin.ps
## }}}

.PHONY: clean
## {{{
clean:
	rm -f busprops.pdf
## }}}
