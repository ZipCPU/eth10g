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

- [UART console via the debugbus](rtl/wbubus/wbuconsole.v)
- [uSD](rtl/sdspi/sdspi.v) (SPI interface control only at present)
- [QSPI Flash](rtl/qflexpress.v)
- [I2C](rtl/wbi2c/wbi2ccpu.v)
  - Si5324 clock generator
  - B/W OLED display
- [SPIO: 5 buttons, 8 LEDs, and 9 switches](rtl/spio.v)
- HDMI RX and TX
- RPi CM4 SMI interface
- SATA
- EMMC

## Sponsorship

This is project is sponsored by Net Idea.

## License

This project is released under the Apache 2 license.

## Status

As of 11 May, 2023:

- The PCB for this project has been built, and is currently under test.

- The project RTL is partially assembled.  Components assembled, attached, and
  (potentially under test) include:
  - The bus itself has been assembled, to include the [Wishbone crossbar](rtl/wb2axip/rtl/wbxbar.v)s, as well as [up](rtl/wb2axip/wbupsz.v) and [down](rtl/wb2axip/wbdown.v) sizing components
  - The [debug bus](https://github.com/ZipCPU/dbgbus), [the ZipCPU](https://github.com/ZipCPU/zipcpu), the [ZipCPU's (new) DMA](rtl/cpu/zipdma.v)
  - The [I2C Controller](rtl/wbi2c/wbi2ccpu.v)
  - [General](rtl/gpio.v) and [Special Purpose IO](rtl/spio.v) controllers
  - [SPI based SD card controller](https://github.com/ZipCPU/sdspi)
  - [Fan control and temperature measurement](rtl/wbfan.v)
  - [Si5324 reference clock controller](https://zipcpu.com/blog/2019/06/28/genclk.html)

- Components not yet integrated include:
  - [SMI Slave Controller](rtl/smi/smi.v)
  - The 10G Ethernet, to include the virtual packet FIFOs
  - The DDR3 SDRAM memory controller
  - [The SATA Controller](https://github.com/ZipCPU/wbsata)
  - HDMI

