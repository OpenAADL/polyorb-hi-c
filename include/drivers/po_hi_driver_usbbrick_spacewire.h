/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2011-2014 ESA & ISAE.
 */

#include <deployment.h>

#include <drivers/configuration/spacewire.h>

#ifndef __PO_HI_DRIVER_USBBRICK_SPACEWIRE_H__
#define __PO_HI_DRIVER_USBBRICK_SPACEWIRE_H__

#ifdef __PO_HI_NEED_DRIVER_SPACEWIRE_USB_BRICK

void __po_hi_c_driver_spw_usb_brick_poller (const __po_hi_device_id dev_id);

void __po_hi_c_driver_spw_usb_brick_init (__po_hi_device_id id);

int __po_hi_c_driver_spw_usb_brick_sender (const __po_hi_task_id task_id, const __po_hi_port_t port);


#endif

#endif



/******************************************************************************/
/*                                                                            */
/*  spw_config_library.h                                                      */
/*                                                                            */
/*  Declaration of the functions, and definition of macros  provided by the   */
/*  SpaceWire Router Configuration Library for the SpaceWire USB and          */
/*  SpaceWire PCI drivers.                                                    */
/*                                                                            */
/*  Version 2.53 - February 26th 2009                                         */
/*                                                                            */
/*      Version 2.53 - 26/02/09                                               */
/*      =======================                                               */
/*      Updated the calling convention used in the function declarations to   */
/*      __stdcall on Windows.                                                 */
/*                                                                            */
/*      Version 2.52, 04/11/08                                                */
/*      ======================                                                */
/*      Added support for precision transmit rate on new Router-USB.          */
/*      Added chip ID values.                                                 */
/*                                                                            */
/*      Version 2.51, 21/10/08                                                */
/*      ======================                                                */
/*      Updated to support Windows.                                           */
/*                                                                            */
/*      Version 2.50, 08/11/06                                                */
/*      ======================                                                */
/*      Initial version, following change to new structure.                   */
/*                                                                            */
/*  Copyright (c) 2009, Stuart Mills,                                         */
/*                      STAR-Dundee,                                          */
/*                      c/o School of Computing,                              */
/*                      University of Dundee,                                 */
/*                      Dundee, DD1 4HN,                                      */
/*                      Scotland, UK.                                         */
/*                      http://www.star-dundee.com                            */
/*              e-mail: stuart@star-dundee.com                                */
/*                                                                            */
/******************************************************************************/



#ifndef SPACEWIRE_ROUTER_LIBRARY
#define SPACEWIRE_ROUTER_LIBRARY


#include "star_dundee_types.h"


#ifdef __cplusplus
extern "C" {
#endif



#if defined(_WIN32) || defined(_WIN64)


/* Windows specifc functions and macros */

#ifdef ROUTERCONFIGURATIONLIBRARY_EXPORTS
#define ROUTER_CONFIG_LIBRARY __declspec(dllexport)
#else
#define ROUTER_CONFIG_LIBRARY __declspec(dllimport)
#endif

/* The calling convention to be used */
#ifdef  _WIN64
#define ROUTER_CONFIG_CC
#else
#define ROUTER_CONFIG_CC __stdcall
#endif	/* WIN64 */


#include "windows.h"

	
#else	/* _WIN32 */


/* Linux specific functions and macros */

#define ROUTER_CONFIG_LIBRARY
#define ROUTER_CONFIG_CC


#endif	/* _WIN32 */



/* Possible bit values */
#define BIT0	(0x00000001)
#define BIT1	(0x00000002)
#define BIT2	(0x00000004)
#define BIT3	(0x00000008)
#define BIT4	(0x00000010)
#define BIT5	(0x00000020)
#define BIT6	(0x00000040)
#define BIT7	(0x00000080)
#define BIT8	(0x00000100)
#define BIT9	(0x00000200)
#define BIT10	(0x00000400)
#define BIT11	(0x00000800)
#define BIT12	(0x00001000)
#define BIT13	(0x00002000)
#define BIT14	(0x00004000)
#define BIT15	(0x00008000)
#define BIT16	(0x00010000)
#define BIT17	(0x00020000)
#define BIT18	(0x00040000)
#define BIT19	(0x00080000)
#define BIT20	(0x00100000)
#define BIT21	(0x00200000)
#define BIT22	(0x00400000)
#define BIT23	(0x00800000)
#define BIT24	(0x01000000)
#define BIT25	(0x02000000)
#define BIT26	(0x04000000)
#define BIT27	(0x08000000)
#define BIT28	(0x10000000)
#define BIT29	(0x20000000)
#define BIT30	(0x40000000)
#define BIT31	(0x80000000)



/* Exported enums and structs */



/* Read write address errors */
typedef enum
{
	CFG_TRANSFER_SUCCESS		= 0x00,
	CFG_TRANSMIT_PACKET_FAILURE	= 0x01,
	CFG_REPLY_PACKET_FAILURE	= 0x02,
	CFG_REPLY_PACKET_TOO_BIG	= 0x03,
	CFG_REPLY_PACKET_TOO_SMALL	= 0x04,
	CFG_REPLY_PACKET_NAK		= 0x05,
	CFG_REPLY_PACKET_CHECKSUM_ERROR	= 0x06,
} CFG_SPACEWIRE_STATUS;



/* Length of port timeout */
typedef enum
{
	CFG_PORT_TIMEOUT_100US     = 0x0,
	CFG_PORT_TIMEOUT_1MS       = 0x1,
	CFG_PORT_TIMEOUT_10MS      = 0x2,
	CFG_PORT_TIMEOUT_100MS     = 0x3,
	CFG_PORT_TIMEOUT_1S        = 0x4,
} CFG_SPACEWIRE_PORT_TIMEOUT;



/* SpaceWire Port errors */
#define CFG_SPACEWIRE_NO_ERRORS			(0)
#define CFG_SPACEWIRE_ERROR_ACTIVE		(BIT0)
#define CFG_SPACEWIRE_PACKET_ADDRESS_ERROR	(BIT1)
#define CFG_SPACEWIRE_PORT_TIMEOUT_ERROR	(BIT2)
#define CFG_SPACEWIRE_DISCONNECT_ERROR		(BIT3)
#define CFG_SPACEWIRE_PARITY_ERROR		(BIT4)
#define CFG_SPACEWIRE_ESCAPE_ERROR		(BIT5)
#define CFG_SPACEWIRE_CREDIT_ERROR		(BIT6)
#define CFG_SPACEWIRE_CHARACTER_SEQUENCE_ERROR	(BIT7)
#define CFG_SPACEWIRE_ERROR_BITS		(BIT0 | BIT1 | BIT2 | BIT3 | \
						BIT4 | BIT5 | BIT6 | BIT7)

/* Config Port errors */
#define CFG_CONFIG_NO_ERRORS			(0)
#define CFG_CONFIG_ERROR_ACTIVE			(BIT0)

/* Config Port errors (non-RMAP) */
#define CFG_CONFIG_PACKET_ADDRESS_ERROR		(BIT1)
#define CFG_CONFIG_PORT_TIMEOUT_ERROR		(BIT2)
#define CFG_CONFIG_CHECKSUM_ERROR		(BIT3)
#define CFG_CONFIG_TOO_SHORT_ERROR		(BIT4)
#define CFG_CONFIG_TOO_LONG_ERROR		(BIT5)
#define CFG_CONFIG_PACKET_EEP_ERROR		(BIT6)
#define CFG_CONFIG_PROTOCOL_BYTE_ERROR		(BIT7)
#define CFG_CONFIG_INVALID_REGISTER_ERROR	(BIT8)
#define CFG_CONFIG_ERROR_BITS			(BIT0 | BIT1 | BIT2 | BIT3 | \
						 BIT4 | BIT5 | BIT6 | BIT7 | \
						 BIT8)

/* Config Port errors (RMAP) */
#define CFG_CONFIG_RMAP_PORT_TIMEOUT_ERROR			(BIT1)
#define CFG_CONFIG_RMAP_INVALID_HEADER_CRC			(BIT2)
#define CFG_CONFIG_RMAP_INVALID_DATA_CRC			(BIT3)
#define CFG_CONFIG_RMAP_INVALID_DESTINATION_KEY			(BIT4)
#define CFG_CONFIG_RMAP_COMMAND_NOT_IMPLEMENTED			(BIT5)
#define CFG_CONFIG_RMAP_INVALID_DATA_LENGTH			(BIT6)
#define CFG_CONFIG_RMAP_INVALID_RMW_DATA_LENGTH			(BIT7)
#define CFG_CONFIG_RMAP_INVALID_DESTINATION_ADDRESS		(BIT8)
#define CFG_CONFIG_RMAP_EARLY_EOP				(BIT9)
#define CFG_CONFIG_RMAP_LATE_EOP				(BIT10)
#define CFG_CONFIG_RMAP_EARLY_EEP				(BIT11)
#define CFG_CONFIG_RMAP_LATE_EEP				(BIT12)
#define CFG_CONFIG_RMAP_VERIFY_BUFFER_OVERRUN_ERROR		(BIT13)
#define CFG_CONFIG_RMAP_INVALID_REGISTER_ADDRESS		(BIT14)
#define CFG_CONFIG_RMAP_UNSUPPORTED_PROTOCOL_ERROR		(BIT15)
#define CFG_CONFIG_RMAP_SOURCE_LOGICAL_ADDRESS_ERROR		(BIT16)
#define CFG_CONFIG_RMAP_SOURCE_PATH_ADDRESS_ERROR		(BIT17)
#define CFG_CONFIG_RMAP_CARGO_TOO_LARGE				(BIT18)
#define CFG_CONFIG_RMAP_UNUSED_COMMAND_OR_PACKET_TYPE		(BIT19)
#define CFG_CONFIG_RMAP_ERROR_BITS	(BIT0 | BIT1 | BIT2 | BIT3 | BIT4 | \
					 BIT5 | BIT6 | BIT7 | BIT8 | BIT9 | \
					 BIT10 | BIT11 | BIT12 | BIT13 | \
					 BIT14 | BIT15 | BIT16 | BIT17 | \
					 BIT18 | BIT19)

/* External Port errors */
#define CFG_EXTERNAL_NO_ERRORS			(0)
#define CFG_EXTERNAL_ERROR_ACTIVE		(BIT0)
#define CFG_EXTERNAL_PACKET_ADDRESS_ERROR	(BIT1)
#define CFG_EXTERNAL_PORT_TIMEOUT_ERROR		(BIT2)
#define CFG_EXTERNAL_INPUT_BUFFER_EMPTY_ERROR	(BIT3)
#define CFG_EXTERNAL_INPUT_BUFFER_FULL_ERROR	(BIT4)
#define CFG_EXTERNAL_OUTPUT_BUFFER_EMPTY_ERROR	(BIT5)
#define CFG_EXTERNAL_OUTPUT_BUFFER_FULL_ERROR	(BIT6)
#define CFG_EXTERNAL_ERROR_BITS			(BIT0 | BIT1 | BIT2 | BIT3 | \
						 BIT4 | BIT5 | BIT6)

/* SpaceWire Port interface state */
#define CFG_SPACEWIRE_ERROR_RESET	(0)
#define CFG_SPACEWIRE_ERROR_WAIT	(BIT0)
#define CFG_SPACEWIRE_READY		(BIT1)
#define CFG_SPACEWIRE_STARTED		(BIT1 | BIT0)
#define CFG_SPACEWIRE_CONNECTING	(BIT2)
#define CFG_SPACEWIRE_RUN		(BIT2 | BIT0)

/* Port type */
#define CFG_CONFIGURATION_PORT		(0)
#define CFG_SPACEWIRE_SERIAL_PORT	(BIT0)
#define CFG_SPACEWIRE_EXTERNAL_PORT	(BIT1)

/* SpaceWire Port control bits */
#define CFG_SPACEWIRE_INTERFACE_STATE_START	(8)
#define CFG_SPACEWIRE_INTERFACE_STATE		(BIT8 | BIT9 | BIT10)
#define CFG_SPACEWIRE_RUNNING			(BIT11)
#define CFG_SPACEWIRE_AUTOSTART			(BIT12)
#define CFG_SPACEWIRE_START			(BIT13)
#define CFG_SPACEWIRE_DISABLE			(BIT14)
#define CFG_SPACEWIRE_TRISTATE			(BIT15)
#define CFG_SPACEWIRE_RATE			(BIT16 | BIT17 | BIT18 | \
						 BIT19 | BIT20 | BIT21 | BIT22)
#define CFG_SPACEWIRE_RATE_START		(16)

/* Bits in the GAR Table */
#define CFG_GAR_OUTPUT_PORTS_START	(1)
#define CFG_GAR_OUTPUT_PORTS		(BIT1 | BIT2 | BIT3 | BIT4 | BIT5 | \
	BIT6 | BIT7 | BIT8 | BIT9 | BIT10 | BIT11 | BIT12 | BIT13 | BIT14 | \
	BIT15 | BIT16 | BIT17 | BIT18 | BIT19 | BIT20 | BIT21 | BIT22 | \
	BIT23 | BIT24 | BIT25 | BIT26 | BIT27 | BIT28)
#define CFG_GAR_DEL_HEAD		(BIT29)
#define CFG_GAR_PRIORITY		(BIT30)
#define CFG_GAR_INVALID_ADDR		(BIT31)

/* Bits in the router control register */
#define CFG_RC_TIMEOUT_ENABLE_START	(0)
#define CFG_RC_TIMEOUT_ENABLE		(BIT0)
#define CFG_RC_TIMEOUT_VALUE_START	(1)
#define CFG_RC_TIMEOUT_VALUE		(BIT1 | BIT2 | BIT3)
#define CFG_RC_DISABLE_ON_SILENCE	(BIT4)
#define CFG_RC_DISABLE_ON_SILENCE_START	(4)
#define CFG_RC_START_ON_REQUEST		(BIT5)
#define CFG_RC_START_ON_REQUEST_START	(5)
#define CFG_RC_SELF_ADDRESSING		(BIT6)
#define CFG_RC_SELF_ADDRESSING_START	(6)
#define CFG_RC_INTERFACE		(BIT7)
#define CFG_RC_INTERFACE_START		(7)
#define CFG_RC_INTERFACE_IDENT		(BIT8)
#define CFG_RC_INTERFACE_IDENT_START	(8)

/* The bits shared by all ports */
#define CFG_PORT_CONNECTION		(BIT24 | BIT25 | BIT26 | BIT27 | BIT28)
#define CFG_PORT_CONNECTION_START	(24)
#define CFG_PORT_TYPE			(BIT29 | BIT30 | BIT31)
#define CFG_PORT_TYPE_START		(29)

/* Network discovery register values */
#define CFG_NETD_TYPE			(BIT0 | BIT1 | BIT2 | BIT3)
#define CFG_NETD_TYPE_START		(0)
#define CFG_NETD_RETURN_PORT		(BIT4 | BIT5 | BIT6 | BIT7)
#define CFG_NETD_RETURN_PORT_START	(4)
#define CFG_NETD_RUNNING_PORTS		(BIT8 | BIT9 | BIT10 | BIT11 | BIT12 | \
	BIT13 | BIT14 | BIT15 | BIT16 | BIT17 | BIT18 | BIT19 | BIT20 | \
	BIT21 | BIT22 | BIT23 | BIT24 | BIT25 | BIT26 | BIT27 | BIT28 | \
	BIT29 | BIT30 | BIT31)
#define CFG_NETD_RUNNING_PORTS_START	(8)

/* Values in the ID register */
#define CFG_ID_VERSION			(BIT0 | BIT1 | BIT2 | BIT3 | BIT4 | \
					 BIT5 | BIT6 | BIT7)
#define CFG_ID_VERSION_START		(0)
#define CFG_ID_CHIP			(BIT8 | BIT9 | BIT10 | BIT11 | BIT12 | \
					 BIT13 | BIT14 | BIT15)
#define CFG_ID_CHIP_START		(8)
#define CFG_ID_MANUFACTURER		(BIT16 | BIT17 | BIT18 | BIT19 | \
					 BIT20 | BIT21 | BIT22 | BIT23)
#define CFG_ID_MANUFACTURER_START	(16)

/* Values in the Time-Code register */
#define CFG_TC_VALUE			(BIT0 | BIT1 | BIT2 | BIT3 | BIT4 | \
					 BIT5)
#define CFG_TC_VALUE_START		(0)
#define CFG_TC_FLAGS			(BIT6 | BIT7)
#define CFG_TC_FLAGS_START		(6)

/* Values for the Router Base Clock Select */
#define CFG_RTR_CLK_100_MBITS		(0)
#define CFG_RTR_CLK_200_MBITS		(BIT0)

/* Values for the Brick Base Clock */
#define CFG_BRK_CLK_100_MHZ		(0)
#define CFG_BRK_CLK_120_MHZ		(BIT0)
#define CFG_BRK_CLK_140_MHZ		(BIT1)
#define CFG_BRK_CLK_160_MHZ		(BIT0 | BIT1)
#define CFG_BRK_CLK_180_MHZ		(BIT2)
#define CFG_BRK_CLK_200_MHZ		(BIT2 | BIT0)

/* Values for the Brick Base Divider */
#define CFG_BRK_DVDR_1			(0)
#define CFG_BRK_DVDR_2			(BIT0)
#define CFG_BRK_DVDR_4			(BIT1)

/* Values in the Tx register */
#define CFG_TX_BRICK_2MBITS		(BIT27)
#define CFG_TX_BRICK_2MBITS_START	(27)

/* Values in the Precision Transmit Rate register */
#define CFG_PT_ENABLE		(BIT16)
#define CFG_PT_ENABLE_START	(16)
#define CFG_PT_READY		(BIT17)
#define CFG_PT_READY_START	(17)
#define CFG_PT_IN_USE		(BIT20)
#define CFG_PT_IN_USE_START	(20)
#define CFG_PT_RATE_BITS	(BIT0 | BIT1 | BIT2 | BIT3 | BIT4 | BIT5 | BIT6 | \
							 BIT7 | BIT8 | BIT9 | BIT10 | BIT11 | BIT12 | \
							 BIT13 | BIT14 | BIT15 )
#define CFG_PT_DIVIDER_CONSTANT	((double)(pow((double)2, (double)48) / (double)600))

/* Chip ID values */
#define CFG_CID_ROUTER_ASIC		(0)		/* SpaceWire Router ASIC and IP */
#define CFG_CID_ROUTER_USB		(1)		/* Original SpaceWire Router-USB */
#define CFG_CID_USB_BRICK		(2)		/* SpaceWire-USB Brick */
#define CFG_CID_FEIC			(4)		/* The FEIC chip */
#define CFG_CID_ROUTER_USB_2	(5)		/* New SpaceWire Router-USB */


/* Addresses which can be read from and written to */
#define CFG_EXTENDED_ADDRESS	(0x100)
#define CFG_ADDR_NET_DISC		(CFG_EXTENDED_ADDRESS + 0)
#define CFG_ADDR_NET_DISC_IDENT	(CFG_EXTENDED_ADDRESS + 1)
#define CFG_ADDR_ROUTER_CONTROL	(CFG_EXTENDED_ADDRESS + 2)
#define CFG_ADDR_ERRORS			(CFG_EXTENDED_ADDRESS + 3)
#define CFG_ADDR_TIMECODE		(CFG_EXTENDED_ADDRESS + 4)
#define CFG_ADDR_IDS			(CFG_EXTENDED_ADDRESS + 5)
#define CFG_ADDR_GP				(CFG_EXTENDED_ADDRESS + 6)
#define CFG_ADDR_TICK			(CFG_EXTENDED_ADDRESS + 7)
#define CFG_ADDR_TX_RATE		(CFG_EXTENDED_ADDRESS + 8)
#define CFG_ADDR_PRECISION_1	(CFG_EXTENDED_ADDRESS + 0xC)
#define CFG_ADDR_PRECISION_2	(CFG_EXTENDED_ADDRESS + 0xD)


/* Exported functions */

/* Version information */
ROUTER_CONFIG_LIBRARY double ROUTER_CONFIG_CC CFGSpaceWire_GetAPIVersion(void);

/* Configuration address stack manipulation functions */
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_StackClear(void);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_AddrStackPush(
	U8 dwAddress);
ROUTER_CONFIG_LIBRARY U8   ROUTER_CONFIG_CC CFGSpaceWire_AddrStackPop(void);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_RetAddrStackPush(
	U8 dwAddress);
ROUTER_CONFIG_LIBRARY U8   ROUTER_CONFIG_CC CFGSpaceWire_RetAddrStackPop(void);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_SetProtocolByte(
	U8 ProtocolByte);
ROUTER_CONFIG_LIBRARY U8   ROUTER_CONFIG_CC CFGSpaceWire_GetProtocolByte(void);

/* RMAP functions */
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_EnableRMAP(
	char useRMAP);
ROUTER_CONFIG_LIBRARY char ROUTER_CONFIG_CC CFGSpaceWire_IsRMAPEnabled();
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_SetRMAPDestinationKey(
	U8 destinationKey);
ROUTER_CONFIG_LIBRARY U8 ROUTER_CONFIG_CC CFGSpaceWire_GetRMAPDestinationKey();
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_SetRMAPAlignment(
	U8 alignment);
ROUTER_CONFIG_LIBRARY U8 ROUTER_CONFIG_CC CFGSpaceWire_GetRMAPAlignment();
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_EnableReadOnAllPorts(
	char enable);
ROUTER_CONFIG_LIBRARY char ROUTER_CONFIG_CC
	CFGSpaceWire_IsReadingOnAllPortsEnabled();

/* Ignoring replies to write commands functions */
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_IgnoreWriteReplies(
	char ignore);
ROUTER_CONFIG_LIBRARY char ROUTER_CONFIG_CC
	CFGSpaceWire_AreWriteRepliesIgnored();

/* Configuration address read and write functions */
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_ReadAddress(
	star_device_handle hDevice, U32 dwAddress, U32 *dwData);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_WriteAddress(
	star_device_handle hDevice, U32 dwAddress, U32 dwData);

/* Router link functions */
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_StartLink(
	star_device_handle hDevice, U32 dwLinkNum);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_StopLink(
	star_device_handle hDevice, U32 dwLinkNum);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_TriStateLink(
	star_device_handle hDevice, U32 dwLinkNum, char bEnabled);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_SetLinkSpeed(
	star_device_handle hDevice, U32 dwLinkNum, U32 dwSpeed);

/* Routing table functions */
ROUTER_CONFIG_LIBRARY int  ROUTER_CONFIG_CC CFGSpaceWire_GetRoutingTableEntry(
	star_device_handle hDevice, U32 nLogicalAddress, U32 *dwRoutingTableEntry);
ROUTER_CONFIG_LIBRARY int  ROUTER_CONFIG_CC CFGSpaceWire_SetRoutingTableEntry(
	star_device_handle hDevice, U32 nLogicalAddress, U32 dwRoutingTableEntry);
ROUTER_CONFIG_LIBRARY int  ROUTER_CONFIG_CC CFGSpaceWire_ClearRoutingTableEntry(
	star_device_handle hDevice, U32 nLogicalAddress);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_RTIsEnabled(
	U32 dwRoutingTableEntry, char *bEnabled);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_RTIsDelHead(
	U32 dwRoutingTableEntry, char *bDelHead);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_RTIsPriority(
	U32 dwRoutingTableEntry, char *bPriority);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_RTOutputPorts(
	U32 dwRoutingTableEntry, U32 *dwOutputPorts);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC
	CFGSpaceWire_RTBuildRoutingTableEntry(U32 *dwRoutingTableEntry,
		U32 dwOutputPorts, char bDelHead, char bPriority);

/* Link status control functions */
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_GetLinkStatusControl(
	star_device_handle hDevice, U32 dwLinkNum, U32 *dwStatusControl);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_SetLinkStatusControl(
	star_device_handle hDevice, U32 dwLinkNum, U32 dwStatusControl);

ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_LSErrorStatus(
	U32 dwStatusControl, U32 *dwErrorStatus);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_LSConfigErrorStatus(
	U32 dwStatusControl, U32 *dwErrorStatus);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_LSExternalErrorStatus(
	U32 dwStatusControl, U32 *dwErrorStatus);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_LSLinkState(
	U32 dwStatusControl, U32 *dwLinkStatus);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_LSIsLinkRunning(
	U32 dwStatusControl, char *isLinkRunning);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_LSIsAutoStart(
	U32 dwStatusControl, char *isAutoStart);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_LSEnableAutoStart(
	U32 *dwStatusControl, char bEnabled);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_LSIsStart(
	U32 dwStatusControl, char *isStart);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_LSEnableStart(
	U32 *dwStatusControl, char bEnabled);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_LSIsDisabled(
	U32 dwStatusControl, char *isDisabled);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_LSEnableDisabled(
	U32 *dwStatusControl, char bEnabled);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_LSIsTristate(
	U32 dwStatusControl, char *isTristate);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_LSEnableTristate(
	U32 *dwStatusControl, char bEnabled);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_LSOperatingSpeed(
	U32 dwStatusControl, U32 *dwOperatingSpeed);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_LSSetOperatingSpeed(
	U32 *dwStatusControl, U32 dwOperatingSpeed);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_LSOutputPortConnection(
	U32 dwStatusControl, U32 *dwOutputPortConnection);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_LSPortType(
	U32 dwStatusControl, U32 *dwPortType);

/* Network discovery information retreival */
ROUTER_CONFIG_LIBRARY int  ROUTER_CONFIG_CC
	CFGSpaceWire_GetNetworkDiscoveryValue(star_device_handle hDevice,
		U32 *dwNetworkDiscovery);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_NDDeviceType(
	U32 dwNetDisc, U32 *dwDeviceType);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_NDReturnPort(
	U32 dwNetDisc, U32 *dwReturnPort);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_NDRunningLinks(
	U32 dwNetDisc, U32 *dwRunningLinks);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_NDNumberLinks(
	U32 dwNetDisc, U32 *dwNumberLinks);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_GetNumberLinks(
	star_device_handle hDevice, U32 *dwNumLinks);

/* Router identity register functions */
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_SetNetworkID(
	star_device_handle hDevice, U32 dwNetworkID);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_GetNetworkID(
	star_device_handle hDevice, U32 *dwNetworkID);

/* Router control register functions */
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_SetPortTimeout(
	star_device_handle hDevice, char bEnabled,
	CFG_SPACEWIRE_PORT_TIMEOUT timeout);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_GetPortTimeout(
	star_device_handle hDevice, char *bEnabled,
	CFG_SPACEWIRE_PORT_TIMEOUT *timeout);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_IsPortTimeoutEnabled(
	star_device_handle hDevice, char *bEnabled);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_SetAsInterface(
	star_device_handle hDevice, char bEnabled, char bAddIdentifier);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC
	CFGSpaceWire_GetRouterControlRegister(star_device_handle hDevice,
		U32 *dwRouterCtrlReg);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC
	CFGSpaceWire_SetRouterControlRegister(star_device_handle hDevice,
		U32 dwRouterCtrlReg);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_RCGetTimeoutEnabled(
	U32 dwRouterCtrlReg, char *bEnabled);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_RCSetTimeoutEnabled(
	U32 *dwRouterCtrlReg, char bEnabled);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_RCGetTimeoutSelection(
	U32 dwRouterCtrlReg, U32 *dwSelection);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_RCSetTimeoutSelection(
	U32 *dwRouterCtrlReg, U32 dwSelection);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_RCGetDisableOnSilence(
	U32 dwRouterCtrlReg, char *bEnabled);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_RCSetDisableOnSilence(
	U32 *dwRouterCtrlReg, char bEnabled);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_RCGetStartOnRequest(
	U32 dwRouterCtrlReg, char *bEnabled);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_RCSetStartOnRequest(
	U32 *dwRouterCtrlReg, char bEnabled);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_RCGetSelfAddressing(
	U32 dwRouterCtrlReg, char *bEnabled);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_RCSetSelfAddressing(
	U32 *dwRouterCtrlReg, char bEnabled);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_RCGetInterface(
	U32 dwRouterCtrlReg, char *bEnabled);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_RCSetInterface(
	U32 *dwRouterCtrlReg, char bEnabled);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC
	CFGSpaceWire_RCGetInterfaceIdentifier(U32 dwRouterCtrlReg, char *bEnabled);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC
	CFGSpaceWire_RCSetInterfaceIdentifier(U32 *dwRouterCtrlReg, char bEnabled);

/* Error active register functions */
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_GetErrorStatus(
	star_device_handle hDevice, U32 *dwErrorStatus);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_ClearErrorStatus(
	star_device_handle hDevice, U32 dwPorts);

/* Time-Code register functions */
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_GetTimecodeRegister(
	star_device_handle hDevice, U32 *dwTimecodeReg);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_TCGetValue(
	U32 dwTimecodeReg, U32 *dwValue);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_TCGetFlags(
	U32 dwTimecodeReg, U32 *dwValue);

/* Manufacturer and Chip ID register functions */
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_GetIDRegister(
	star_device_handle hDevice, U32 *dwIDs);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_IDGetManufacturer(
	U32 dwIDs, U32 *dwManufacturerID);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_IDGetChipID(U32 dwIDs,
	U32 *dwChipID);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC CFGSpaceWire_IDGetVersion(U32 dwIDs,
	U32 *dwVersion);

/* General purpose register functions */
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_GetGeneralPurposeStatus(
	star_device_handle hDevice, U32 *dwGeneralPurposeStatus);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_SetGeneralPurposeStatus(
	star_device_handle hDevice, U32 dwGeneralPurposeStatus);

/* Tick enable register functions */
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_GetTickEnableStatus(
	star_device_handle hDevice, U32 *dwTickEnableStatus);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC CFGSpaceWire_SetTickEnableStatus(
	star_device_handle hDevice, U32 dwTickEnableStatus);


/* Base Transmit Rate functions */
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC
	CFGSpaceWire_SetRouterBaseTransmitRate(star_device_handle hDevice,
		U32 dwBaseClkSel);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC
	CFGSpaceWire_GetRouterBaseTransmitRate(star_device_handle hDevice,
		U32 *dwBaseClkSel);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC
	CFGSpaceWire_SetBrickBaseTransmitRate(star_device_handle hDevice,
		U32 dwBaseClk, U32 dwBaseDvdr, U32 dwEnableClk);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC
	CFGSpaceWire_GetBrickBaseTransmitRate(star_device_handle hDevice,
		U32 *dwBaseClk, U32 *dwBaseDvdr, U32 *dwEnableClk);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC
	CFGSpaceWire_GetPrecisionTransmitRegister(star_device_handle hDevice,
		U32 *dwPrecisionTransmit);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC
	CFGSpaceWire_SetPrecisionTransmitRegister(star_device_handle hDevice,
		U32 dwPrecisionTransmit);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC
	CFGSpaceWire_PTGetPrecisionTransmitEnabled(U32 dwPrecisionTransmit,
		char *bEnabled);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC
	CFGSpaceWire_PTSetPrecisionTransmitEnabled(U32 *dwPrecisionTransmit,
		char bEnabled);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC
	CFGSpaceWire_PTGetPrecisionTransmitReady(U32 dwPrecisionTransmit,
		char *bEnabled);
ROUTER_CONFIG_LIBRARY void ROUTER_CONFIG_CC
	CFGSpaceWire_PTGetPrecisionTransmitInUse(U32 dwPrecisionTransmit,
		char *bEnabled);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC
	CFGSpaceWire_GetPrecisionTransmitRate(star_device_handle hDevice,
		double *PrecisionTransmitRate);
ROUTER_CONFIG_LIBRARY int ROUTER_CONFIG_CC
	CFGSpaceWire_SetPrecisionTransmitRate(star_device_handle hDevice,
		double PrecisionTransmitRate);



#ifdef __cplusplus
}
#endif



#endif	/* SPACEWIRE_ROUTER_LIBRARY */


/******************************************************************************/
/*                                                                            */
/*  spw_usb_api.h                                                             */
/*                                                                            */
/*  Declaration of the functions provided by the SpaceWire USB API Library    */
/*  for the SpaceWire USB devices.                                            */
/*                                                                            */
/*  Version 1.5, March 12th 2010                                              */
/*                                                                            */
/*      Version 1.5, 12/03/10                                                 */
/*      =====================                                                 */
/*      Added GetFirmwareVersionExtended and restored GetFirmwareVersion to   */
/*      its original form.                                                    */
/*                                                                            */
/*      Version 1.4, 03/03/10                                                 */
/*      =====================                                                 */
/*      Fixed bug waiting on a receive to complete.                           */
/*      Added support for multiple send channels.                             */
/*      Added functions to get serial number and product ID.                  */
/*                                                                            */
/*      Version 1.3, 26/2/09                                                  */
/*      ====================                                                  */
/*      Updated the calling convention used in the function declaration to    */
/*      __stdcall on Windows.                                                 */
/*                                                                            */
/*      Version 1.2, 21/1/09                                                  */
/*      ====================                                                  */
/*      Updated to compile on both Windows and Linux.                         */
/*                                                                            */
/*      Version 1.1, 8/10/06                                                  */
/*      ====================                                                  */
/*      Linux release.                                                        */
/*                                                                            */
/*      Version 1.0, 24/4/06                                                  */
/*      ====================                                                  */
/*      Initial version.                                                      */
/*                                                                            */
/*  Copyright (c) 2009, Stuart Mills,                                         */
/*                      STAR-Dundee,                                          */
/*                      c/o School of Computing,                              */
/*                      University of Dundee,                                 */
/*                      Dundee, DD1 4HN,                                      */
/*                      Scotland, UK.                                         */
/*              e-mail: stuart@star-dundee.com                                */
/*                                                                            */
/******************************************************************************/



#ifndef SPACEWIRE_USB_API_H
#define SPACEWIRE_USB_API_H




#ifdef __cplusplus
extern "C" {
#endif



#include "spacewire_usb.h"



#if defined(_WIN32) || defined(_WIN64)


/* Windows specifc functions and macros */

#ifdef SPACEWIREUSBAPI_EXPORTS
#define SPACEWIREUSB_API __declspec(dllexport)
#else
#define SPACEWIREUSB_API __declspec(dllimport)
#endif

#ifdef  _WIN64
#define SPW_USB_API_CC
#else
#define SPW_USB_API_CC __stdcall
#endif	/* WIN64 */


#include "windows.h"

	
#else	/* _WIN32 */


/* Linux specific functions and macros */

#define SPACEWIREUSB_API
#define SPW_USB_API_CC


#endif	/* _WIN32 */



/* Functions provided by the API */

/* General functions */
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_Open(
	star_device_handle *phDevice, int nDeviceNum);
SPACEWIREUSB_API void SPW_USB_API_CC USBSpaceWire_Close(
	star_device_handle hDevice);
SPACEWIREUSB_API U8 SPW_USB_API_CC USBSpaceWire_CountDevices();
SPACEWIREUSB_API U32 SPW_USB_API_CC USBSpaceWire_ListDevices();
SPACEWIREUSB_API double SPW_USB_API_CC USBSpaceWire_GetDriverVersion();
SPACEWIREUSB_API double SPW_USB_API_CC USBSpaceWire_GetIFVersion();
SPACEWIREUSB_API double SPW_USB_API_CC USBSpaceWire_GetAPIVersion();
SPACEWIREUSB_API void SPW_USB_API_CC USBSpaceWire_SetTimeout(
	star_device_handle hDevice, double timeout);
SPACEWIREUSB_API double SPW_USB_API_CC USBSpaceWire_GetTimeout(
	star_device_handle hDevice);
SPACEWIREUSB_API U8 SPW_USB_API_CC USBSpaceWire_GetSpaceWireAddress(
	star_device_handle hDevice);
SPACEWIREUSB_API void SPW_USB_API_CC USBSpaceWire_SetSpaceWireAddress(
	star_device_handle hDevice, U8 address);
SPACEWIREUSB_API U16 SPW_USB_API_CC USBSpaceWire_GetFirmwareVersion(
	star_device_handle hDevice);
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_GetFirmwareVersionExtended(
	star_device_handle hDevice, SPACEWIRE_FIRMWARE_VERSION *pVersion);
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_ClearEndpoints(
	star_device_handle hDevice);
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_ResetDevice(
	star_device_handle hDevice);
SPACEWIREUSB_API SPACEWIRE_DEVICE_TYPE SPW_USB_API_CC
	USBSpaceWire_GetDeviceType(star_device_handle hDevice);
SPACEWIREUSB_API SPACEWIRE_DEVICE_TYPE SPW_USB_API_CC
	USBSpaceWire_GetUnopenedDeviceType(int deviceNum);
SPACEWIREUSB_API U16 SPW_USB_API_CC USBSpaceWire_GetDeviceProductID(
	star_device_handle hDevice);
SPACEWIREUSB_API U16 SPW_USB_API_CC USBSpaceWire_GetUnopenedDeviceProductID(
	int deviceNum);
SPACEWIREUSB_API void SPW_USB_API_CC USBSpaceWire_EnableHeaderMode(
	star_device_handle hDevice, char enable);
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_IsHeaderModeEnabled(
	star_device_handle hDevice);
SPACEWIREUSB_API void SPW_USB_API_CC USBSpaceWire_EnableNetworkMode(
	star_device_handle hDevice, char enable);
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_IsNetworkModeEnabled(
	star_device_handle hDevice);
SPACEWIREUSB_API double SPW_USB_API_CC USBSpaceWire_GetUSBVersion(
	star_device_handle hDevice);
SPACEWIREUSB_API void SPW_USB_API_CC USBSpaceWire_GetAPIString(char *str);
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_GetSerialNumber(
	star_device_handle hDevice, U8 pSerialNumber[11]);

/* Receive functions */
SPACEWIREUSB_API unsigned long SPW_USB_API_CC
	USBSpaceWire_GetDriverDroppedPackets(star_device_handle hDevice);
SPACEWIREUSB_API unsigned long SPW_USB_API_CC
	USBSpaceWire_GetDriverDroppedBytes(star_device_handle hDevice);
SPACEWIREUSB_API unsigned long SPW_USB_API_CC USBSpaceWire_GetDroppedPackets(
	star_device_handle hDevice);
SPACEWIREUSB_API unsigned long SPW_USB_API_CC USBSpaceWire_GetDroppedBytes(
	star_device_handle hDevice);
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_RegisterReceiveOnPort(
	star_device_handle hDevice, U8 port);
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_UnregisterReceiveOnPort(
	star_device_handle hDevice, U8 port);
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_RegisterReceiveOnAllPorts(
	star_device_handle hDevice);
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_UnregisterReceiveOnAllPorts(
	star_device_handle hDevice);
SPACEWIREUSB_API USB_SPACEWIRE_STATUS SPW_USB_API_CC USBSpaceWire_ReadPackets(
	star_device_handle hDevice, void *pBuffer, U32 nBufferSize,
	U32 nPacketNum, char bWait, PUSB_SPACEWIRE_PACKET_PROPERTIES properties,
	USB_SPACEWIRE_ID *identifier);
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_FreeRead(
	star_device_handle hDevice, USB_SPACEWIRE_ID identifier);
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_FreeAllReads(
	star_device_handle hDevice);
SPACEWIREUSB_API USB_SPACEWIRE_STATUS SPW_USB_API_CC USBSpaceWire_GetReadStatus(
	star_device_handle hDevice, USB_SPACEWIRE_ID identifier);
SPACEWIREUSB_API USB_SPACEWIRE_STATUS SPW_USB_API_CC
	USBSpaceWire_WaitOnReadCompleting(star_device_handle hDevice,
		USB_SPACEWIRE_ID identifier, char bWaitIndefinitely);
SPACEWIREUSB_API void SPW_USB_API_CC USBSpaceWire_EnableReadThrottling(
	star_device_handle hDevice, char enable);
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_IsReadThrottling(
	star_device_handle hDevice);
SPACEWIREUSB_API void SPW_USB_API_CC USBSpaceWire_SetDriverReadBufferSize(
	star_device_handle hDevice, unsigned long nBufferSize);
SPACEWIREUSB_API unsigned long SPW_USB_API_CC
	USBSpaceWire_GetDriverReadBufferSize(star_device_handle hDevice);
SPACEWIREUSB_API void SPW_USB_API_CC USBSpaceWire_SetDriverReadStructsNum(
	star_device_handle hDevice, unsigned long nStructsNum);
SPACEWIREUSB_API unsigned long SPW_USB_API_CC
	USBSpaceWire_GetDriverReadStructsNum(star_device_handle hDevice);
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_WaitOnReadPacketAvailable(
	star_device_handle hDevice, double timeout);
SPACEWIREUSB_API U32 SPW_USB_API_CC USBSpaceWire_GetReadLength(
	PUSB_SPACEWIRE_PACKET_PROPERTIES pProperties, U32 nPacketNum);
SPACEWIREUSB_API USB_SPACEWIRE_EOP_TYPE SPW_USB_API_CC
	USBSpaceWire_GetReadEOPStatus(PUSB_SPACEWIRE_PACKET_PROPERTIES pProperties,
		U32 nPacketNum);
SPACEWIREUSB_API SPACEWIRE_TRAFFIC_TYPE SPW_USB_API_CC
	USBSpaceWire_GetReadTrafficType(
		PUSB_SPACEWIRE_PACKET_PROPERTIES pProperties, U32 nPacketNum);

/* Send functions */
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_GetNumberOfSendChannels(
	star_device_handle hDevice);
SPACEWIREUSB_API USB_SPACEWIRE_STATUS SPW_USB_API_CC USBSpaceWire_SendPacketTo(
	star_device_handle hDevice, void *pBuffer, U32 nBufferSize,
	U8 *pAddress, U32 nAddressLen, char bWait,
	USB_SPACEWIRE_ID *identifier);
SPACEWIREUSB_API USB_SPACEWIRE_STATUS SPW_USB_API_CC
	USBSpaceWire_SendPacketToOverChannel(star_device_handle hDevice, U8 channel,
		void *pBuffer, U32 nBufferSize, U8 *pAddress, U32 nAddressLen,
		char bWait, USB_SPACEWIRE_ID *identifier);
SPACEWIREUSB_API USB_SPACEWIRE_STATUS SPW_USB_API_CC
	USBSpaceWire_SendMultiplePacketsTo(star_device_handle hDevice,
		void *pBuffer, U32 nPacketSize, U32 nBufferSize, U8 *pAddress,
		U32 nAddressLen, char bWait, USB_SPACEWIRE_ID *identifier);
SPACEWIREUSB_API USB_SPACEWIRE_STATUS SPW_USB_API_CC
	USBSpaceWire_SendMultiplePacketsToOverChannel(star_device_handle hDevice,
		U8 channel, void *pBuffer, U32 nPacketSize, U32 nBufferSize,
		U8 *pAddress, U32 nAddressLen, char bWait,
		USB_SPACEWIRE_ID *identifier);
SPACEWIREUSB_API USB_SPACEWIRE_STATUS SPW_USB_API_CC
	USBSpaceWire_SendMultiplePacketLengthsTo(star_device_handle hDevice,
		void **pBuffers, U32 *pPacketSizes, U32 nNumberOfPackets, U8 *pAddress,
		U32 nAddressLen, char bWait, USB_SPACEWIRE_ID *identifier);
SPACEWIREUSB_API USB_SPACEWIRE_STATUS SPW_USB_API_CC
	USBSpaceWire_SendMultiplePacketLengthsToOverChannel(
		star_device_handle hDevice, U8 channel, void **pBuffers,
		U32 *pPacketSizes, U32 nNumberOfPackets, U8 *pAddress, U32 nAddressLen,
		char bWait, USB_SPACEWIRE_ID *identifier);
SPACEWIREUSB_API USB_SPACEWIRE_STATUS SPW_USB_API_CC USBSpaceWire_SendPacket(
	star_device_handle hDevice, void *pBuffer, U32 nBufferSize, char bWait,
	USB_SPACEWIRE_ID *identifier);
SPACEWIREUSB_API USB_SPACEWIRE_STATUS SPW_USB_API_CC
	USBSpaceWire_SendPacketOverChannel(star_device_handle hDevice, U8 channel,
		void *pBuffer, U32 nBufferSize, char bWait,
		USB_SPACEWIRE_ID *identifier);
SPACEWIREUSB_API USB_SPACEWIRE_STATUS SPW_USB_API_CC
	USBSpaceWire_SendMultiplePackets(star_device_handle hDevice, void *pBuffer,
		U32 nPacketSize, U32 nBufferSize, char bWait,
		USB_SPACEWIRE_ID *identifier);
SPACEWIREUSB_API USB_SPACEWIRE_STATUS SPW_USB_API_CC
	USBSpaceWire_SendMultiplePacketsOverChannel(star_device_handle hDevice,
		U8 channel, void *pBuffer, U32 nPacketSize, U32 nBufferSize, char bWait,
		USB_SPACEWIRE_ID *identifier);
SPACEWIREUSB_API USB_SPACEWIRE_STATUS SPW_USB_API_CC
	USBSpaceWire_SendMultiplePacketLengths(star_device_handle hDevice,
		void **pBuffers, U32 *pPacketSizes, U32 nNumberOfPackets, char bWait,
		USB_SPACEWIRE_ID *identifier);
SPACEWIREUSB_API USB_SPACEWIRE_STATUS SPW_USB_API_CC
	USBSpaceWire_SendMultiplePacketLengthsOverChannel(
		star_device_handle hDevice, U8 channel, void **pBuffers,
		U32 *pPacketSizes, U32 nNumberOfPackets, char bWait,
		USB_SPACEWIRE_ID *identifier);
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_FreeSend(
	star_device_handle hDevice, USB_SPACEWIRE_ID identifier);
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_FreeAllSends(
	star_device_handle hDevice);
SPACEWIREUSB_API USB_SPACEWIRE_STATUS SPW_USB_API_CC USBSpaceWire_GetSendStatus(
	star_device_handle hDevice, USB_SPACEWIRE_ID identifier);
SPACEWIREUSB_API USB_SPACEWIRE_STATUS SPW_USB_API_CC
	USBSpaceWire_WaitOnSendCompleting(star_device_handle hDevice,
		USB_SPACEWIRE_ID identifier, char bWaitIndefinitely);
SPACEWIREUSB_API U32 SPW_USB_API_CC USBSpaceWire_GetSendSize(
	star_device_handle hDevice, USB_SPACEWIRE_ID identifier);
SPACEWIREUSB_API void SPW_USB_API_CC USBSpaceWire_SetDriverSendBufferSize(
	star_device_handle hDevice, U32 nBufferSize);
SPACEWIREUSB_API U32 SPW_USB_API_CC USBSpaceWire_GetDriverSendBufferSize(
	star_device_handle hDevice);
SPACEWIREUSB_API void SPW_USB_API_CC USBSpaceWire_EnableSendEEPs(
	star_device_handle hDevice, char enable);
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_IsSendEEPsEnabled(
	star_device_handle hDevice);
SPACEWIREUSB_API USB_SPACEWIRE_STATUS SPW_USB_API_CC
	USBSpaceWire_TunnelSendTraffic(star_device_handle hDevice,
		SPACEWIRE_TRAFFIC_TYPE type, void *pBuffer, U32 nBufferSize,
		USB_SPACEWIRE_EOP_TYPE eop, U8 port, char bWait,
		USB_SPACEWIRE_ID *identifier);

/* Time-code functions */
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_TC_PerformTickIn(
	star_device_handle hDevice, U8 timein);
SPACEWIREUSB_API char SPW_USB_API_CC
	USBSpaceWire_TC_EnableExternalTimecodeSelection(star_device_handle hDevice,
		char enable);
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_TC_Reset(
	star_device_handle hDevice);
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_TC_EnableAutoTickIn(
	star_device_handle hDevice, char enableAutoTickIns, char enableAllPorts);
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_TC_SetAutoTickInFrequency(
	star_device_handle hDevice, U32 frequency);
SPACEWIREUSB_API char SPW_USB_API_CC USBSpaceWire_TC_StartReadingTimecodes(
	star_device_handle hDevice, void *arg, void (*callbackfunc)(
	star_device_handle hDevice, U8 timecode, void *arg));
SPACEWIREUSB_API void SPW_USB_API_CC USBSpaceWire_TC_StopReadingTimecodes(
	star_device_handle hDevice);
SPACEWIREUSB_API U32 SPW_USB_API_CC USBSpaceWire_TC_GetClockFrequency(
	star_device_handle hDevice);



#ifdef __cplusplus
}
#endif



#endif	/* SPACEWIRE_USB_API_H */
