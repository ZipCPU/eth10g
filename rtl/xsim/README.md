# Simulation Stubs

This directory exists simply to help me run Verilator on the top level design.
It contains pseudoreplacements, written in Verilog, for a variety of Xilinx
IO macros.

- `BUFG.v` -- Replicates a clock buffer.
- `IBUFDS_GTE2.v` -- Clock input to GTX
- `IBUFDS.v` -- Differential IO input buffer
- `IOBUF.v` -- Tristate IO control

## Status

These files are intended for lint purposes only at this time, and only
perform a minimum functional purpose.  Further, they are not simulatable--just
lint capable.
