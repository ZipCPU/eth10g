#!/bin/bash
################################################################################
##
## Filename:	vversion.sh
## {{{
## Project:	10Gb Ethernet switch
##
## Purpose:	To determine whether or not the verilator prefix for internal
##		variables is v__DOT__ or the name of the top level followed by
##	__DOT__.  If it is the later, output -DNEW_VERILATOR, else be silent.
##
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
if [[ x${VERILATOR_ROOT} != "x" && -x ${VERILATOR_ROOT}/bin/verilator ]];
then
  export VERILATOR=${VERILATOR_ROOT}/bin/verilator
fi
if [[ ! -x ${VERILATOR} ]];
then
  export VERILATOR=verilator
fi
if [[ ! -x `which ${VERILATOR}` ]];
then
  echo "Verilator not found in environment or in path"
  exit -1
fi

VVERLINE=`${VERILATOR} -V | grep -i ^Verilator`
VVER=`echo ${VVERLINE} | cut -d " " -f 2`
LATER=`echo $VVER \>= 3.9 | bc`
if [[ $LATER > 0 ]];
then
  RLATER=`echo $VVER \>= 4.2 | bc`
  if [[ $RLATER > 0 ]];
  then
    ## I'm not quite certain when Verilator started requiring a further
    ## subreference through rootp-> and including the Vdesgin___024root.h
    ## include file.  My best guess is that it is Verilator 4.2, but I don't
    ## know that for certain.  What I do know is that on the development
    ## verrsion 4.211, it requires different semantics to peek at register
    ## names.  This is our attempt to capture that dependency.
    echo "-DROOT_VERILATOR"
  else
    echo "-DNEW_VERILATOR"
  fi
else
  echo "-DOLD_VERILATOR"
fi
exit 0
