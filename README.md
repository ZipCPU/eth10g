# An Open Source 10Gb Ethernet Switch

The main goal of this project is to demonstrate a 10Gb Ethernet switch.
Packets will arrive in one of four SFP+ interfaces, and from there be routed
as appropriately.

## Routing algorithm

The current (draft) routing algorithm is as follows:

1. For each incoming packet, its incoming port and source MAC address will be
   recorded in a table.

   - The table will have timeouts for all entries.
   - If the table is full, the new entry will overwrite the oldest entry

2. For each outgoing packet, if the destination MAC address matches the
   source address seen on a previous incoming source MAC address, the packet
   will be routed to that port.

3. In all other cases, if the port cannot be determined or if the destination
   port is to a broadcast address, the packet will be broadcast to all (other)
   ports.

4. One address will be reserved for a local soft-core CPU.

## Other hardware interfaces

Other hardware interfaces may also be present within this design, to include
UART, HDMI Tx and Rx, a SATA controller, micro SD, eMMC, QSPI flash, I2C,
temperature sensing and fan control, and much more.

## Sponsorship

This is project is sponsored by Net Idea.

## License

This project is released under the Apache 2 license.

## Status

As of Feb, 2023:

- The PCB for this project is currently being designed.  It has not yet
  entered the manufacturing stage.

- The project RTL is currently in a draft assembly status.  Verification
  work has not yet started, much less any hardware implementations.

