#!bin/bash

./wbregs flashcfg 0x0001100	# Activate config mode
./wbregs flashcfg 0x00010ff	# Send 16(*4) bits of ones, break the mode
./wbregs flashcfg 0x00010ff
./wbregs flashcfg 0x0001100	# Inactivate the port

# Reset the SCOPE
./wbregs flashscope 0x0c07ffff
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

echo Configuration register, CR1
./wbregs flashcfg 0x0001035	# Read flag status register
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001100	#

echo "Status register 2 (SR2)"
./wbregs flashcfg 0x0001007	#
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001100	#

echo "AutoBoot register"
./wbregs flashcfg 0x0001014	#
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001100	#

echo "Bank Address Register"
./wbregs flashcfg 0x00010b9	#
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001100	#

echo "ECC Status Register (ECCSR)"
./wbregs flashcfg 0x0001018	#
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001100	#

echo "ASP Register (ASPR)"
./wbregs flashcfg 0x000102b	#
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001100	#

# echo Write enable
# ./wbregs flashcfg 0x0001006	#
# ./wbregs flashcfg 0x0001100	#

# echo Write to the Volatile configuration register, enable XIP
# ./wbregs flashcfg 0x0001081	#
# ./wbregs flashcfg 0x00010f3	#
# ./wbregs flashcfg 0x0001100	#

# echo "Read Volatile configuration register (again)"
# ./wbregs flashcfg 0x0001085	#
# ./wbregs flashcfg 0x0001000	#
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001100	#

echo Return to QSPI
./wbregs flashcfg 0x00010ec	# Return us to QSPI mode, via QIO_READ cmd
./wbregs flashcfg 0x0001a00	# dummy address
./wbregs flashcfg 0x0001a00	# dummy address
./wbregs flashcfg 0x0001a00	# dummy address
./wbregs flashcfg 0x0001a00	# dummy address
./wbregs flashcfg 0x0001aa0	# mode byte
./wbregs flashcfg 0x0001800	# empty byte, switching directions
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
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001800	# Read a byte of data
# ./wbregs flashcfg
# ./wbregs flashcfg 0x0001900	# Raise (deactivate) CS_n
# ./wbregs flashcfg 0x0000100	# Return to user mode
# 
# ./wbregs 0x06000000
# ./wbregs 0x06000004
# ./wbregs 0x06000008
# ./wbregs 0x0600000c
# ./wbregs 0x06000010
# ./wbregs 0x06000014
# ./wbregs 0x06000018
# ./wbregs 0x0600001c
# ./wbregs 0x06000020
# ./wbregs 0x06000024
# ./wbregs 0x06000028
# ./wbregs 0x0600002c
