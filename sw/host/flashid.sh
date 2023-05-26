#!bin/bash
./wbregs flashscope 0x04000000	# Reset flash, disable the trigger
sleep 1

./wbregs flashcfg 0x0001100	# Activate config mode
./wbregs flashcfg 0x00010ff	# Send 16(*4) bits of ones, break the mode
./wbregs flashcfg 0x00010ff
./wbregs flashcfg 0x00010ff
./wbregs flashcfg 0x0001100	# Inactivate the port

# Reset the SCOPE
# echo READ-ID
./wbregs flashcfg 0x000109f	# Issue the read ID command
./wbregs flashcfg 0x0001000	# Read the ID
./wbregs flashcfg
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001100	# End the command

echo Status register
./wbregs flashcfg 0x0001005	# Read status register
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001100	#

echo Flag status register
./wbregs flashcfg 0x0001070	# Read flag status register
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001100	#

echo Non-Volatile configuration register
./wbregs flashcfg 0x00010b5	# Read non-vol config register
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001100	#

echo "Volatile Configuration register"
./wbregs flashcfg 0x0001085	# Read vol config register
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg		## 0xFB = 15 dummy clocks, XIP disabled, WRAP=continuous
./wbregs flashcfg 0x0001100	#

echo "Enhanced Volatile configuration register"
./wbregs flashcfg 0x0001065	#
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001100	#
# 
echo "Extended address register"
./wbregs flashcfg 0x00010c8	#
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001100	#

echo "Gen Purpose read register"
./wbregs flashcfg 0x0001096	#
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001100	#

echo Write enable
./wbregs flashcfg 0x0001006	#
./wbregs flashcfg 0x0001100	#

echo Write to the Volatile configuration register, enable XIP
./wbregs flashcfg 0x0001081	#
./wbregs flashcfg 0x0001083	#
./wbregs flashcfg 0x0001100	#

echo "Read Volatile configuration register (again)"
./wbregs flashcfg 0x0001085	#
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001100	#

echo Return to QSPI
./wbregs flashcfg 0x00010ec	# Return us to QSPI mode, via QIO_READ cmd
./wbregs flashcfg 0x0001a00	# dummy address
./wbregs flashcfg 0x0001a00	# dummy address
./wbregs flashcfg 0x0001a00	# dummy address
./wbregs flashcfg 0x0001a00	# dummy address
./wbregs flashcfg 0x0001aa0	# mode byte
./wbregs flashcfg 0x0001800	# Dummy cycle, switching directions
./wbregs flashcfg 0x0001800	# Dummy clock cycle
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Dummy cycle
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001800	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001900	# Raise (deactivate) CS_n
./wbregs flashcfg 0x0000100	# Return to user mode
# 
./wbregs 0x02e00000
./wbregs 0x02e00004
./wbregs 0x02e00008
./wbregs 0x02e0000c
./wbregs 0x02e00010
./wbregs 0x02e00014
./wbregs 0x02e00018
./wbregs 0x02e0001c
./wbregs 0x02e00020
./wbregs 0x02e00024
./wbregs 0x02e00028
./wbregs 0x02e0002c
./wbregs flashscope 0x8c000000	# Trigger the flash w/o a reset
