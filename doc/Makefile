################################################################################
##
## Filename:	Makefile
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
