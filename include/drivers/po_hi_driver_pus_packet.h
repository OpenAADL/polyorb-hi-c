/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2010-2014 ESA & ISAE.
 */


#ifndef __PO_HI_DRIVER_PUS_PACKET_H__
#define __PO_HI_DRIVER_PUS_PACKET_H__

/*
 * This correspond to the definition of PUS packets.
 * For more information about PUS, please refer
 * to the ECSS standard ECSS-E-70-41A.
 */

#include <po_hi_types.h>

#define PO_HI_DRIVER_PUS_PACKET_VERSION 0

#define PO_HI_DRIVER_PUS_PACKET_TYPE_TM 0
#define PO_HI_DRIVER_PUS_PACKET_TYPE_TC 1

#define PO_HI_DRIVER_PUS_PACKET_SEQUENCE_FLAGS_FIRST        1
#define PO_HI_DRIVER_PUS_PACKET_SEQUENCE_FLAGS_CONTINUATION 0
#define PO_HI_DRIVER_PUS_PACKET_SEQUENCE_FLAGS_LAST         1<<1
#define PO_HI_DRIVER_PUS_PACKET_SEQUENCE_FLAGS_STANDALONE   (1<<1)|1

#define PO_HI_DRIVER_PUS_PACKET_ACK_ACCEPTANCE              1
#define PO_HI_DRIVER_PUS_PACKET_ACK_EXECUTION_START         1<<1
#define PO_HI_DRIVER_PUS_PACKET_ACK_EXECUTION_PROGRESS      1<<2
#define PO_HI_DRIVER_PUS_PACKET_ACK_EXECUTION_COMPLETION    1<<3

typedef enum
{
      __PO_HI_DRIVER_PUS_PACKET_ERROR_NO_ERROR           = 0,
      __PO_HI_DRIVER_PUS_PACKET_ERROR_VERSION            = 1,
      __PO_HI_DRIVER_PUS_PACKET_ERROR_FLAG               = 2,
      __PO_HI_DRIVER_PUS_PACKET_ERROR_DATA_CCSDS_FLAG    = 3
}__po_hi_driver_pus_packet_error_t;

typedef enum
{
      __PO_HI_DRIVER_PUS_SERVICE_VERIFICATION            = 1,
      __PO_HI_DRIVER_PUS_SERVICE_DEVICE_COMMAND          = 2,
      __PO_HI_DRIVER_PUS_SERVICE_HOUSEKEEPING            = 3,
      __PO_HI_DRIVER_PUS_SERVICE_PARAMETER_STATISTICS    = 4,
      __PO_HI_DRIVER_PUS_SERVICE_EVENT_REPORTING         = 5,
      __PO_HI_DRIVER_PUS_SERVICE_MEMORY_MGMT             = 6,
      __PO_HI_DRIVER_PUS_SERVICE_FUNCTION_MGMT           = 8,
      __PO_HI_DRIVER_PUS_SERVICE_TIME_MGMT               = 9,
      __PO_HI_DRIVER_PUS_SERVICE_SCHEDULING              = 11,
      __PO_HI_DRIVER_PUS_SERVICE_MONITORING              = 12,
      __PO_HI_DRIVER_PUS_SERVICE_DATA_TRANSFER           = 13,
      __PO_HI_DRIVER_PUS_SERVICE_FORWARDING              = 14,
      __PO_HI_DRIVER_PUS_SERVICE_STORAGE                 = 15,
      __PO_HI_DRIVER_PUS_SERVICE_TEST                    = 17,
      __PO_HI_DRIVER_PUS_SERVICE_OPERATIONS_PROCEDURE    = 18,
      __PO_HI_DRIVER_PUS_SERVICE_EVENT_ACTION            = 19,
      __PO_HI_DRIVER_PUS_SERVICE_UNUSED                  = 25
}__po_hi_driver_pus_service_t;


typedef struct
{
      struct
      {
            unsigned version :3;
            /* Version = 0, only one version at this time. */
            unsigned type :1;
            /* Type of the packet : TC or TM. */
            unsigned flag :1; 
            /* Set to 1 if the packet has data, 0 otherwise */
            /* TC packet have data, so TC packets must have */
            /* this bit set to 1. */
            unsigned apid :11;
            /* Application-ID whichi is the destination of
             * the packet. APID definition are mission-specific.
             */
      } id;

      struct
      {
            unsigned flags :2;
            /*
             * See maccro PO_HI_DRIVER_PUS_PACKET_SEQUENCE_FLAGS_FIRST 
             * for more information.
             */

            unsigned count :14;
            /*
             * Used to identify uniquely each TC packet.
             */
      } seq_control;

      __po_hi_uint16_t length;
}__po_hi_driver_pus_packet_header_t;

typedef struct
{
      struct
      {
            unsigned ccsds_secondary_flag :1;
            /*
             * Must be set to 0.
             */

            unsigned pus_version_number   :3;
            /*
             * TC packet PUS version number.
             * Must be set to 1.
             */

            unsigned ack                  :4;
            /*
             * Specify the acceptance or the status of a TC.
             * See maccros PO_HI_DRIVER_PUS_PACKET_ACK_*
             * for the possible values.
             */

            __po_hi_uint8_t sid;       /* Service type    */
            /*
             * Values from 0 to 127 are PUS-related
             * Values from 128 to 255 are mission specific.
             */

            __po_hi_uint8_t ssid;      /* Service subtype */
            /*
             * If 0 < sid < 127, values from 0 to 127 are PUS-specific
             * and values from 128 to 255 are mission-specific.
             * If 128 < sid < 255, values from 0 to 255 are mission-specific.
             */

            char* source_id;           /* Optional */
            char* spare;               /* Optional */
      }header;

      char*             application_data;
      char*             spare;
      __po_hi_uint16_t  error_control;
}__po_hi_driver_pus_packet_data_t;

typedef struct
{
   __po_hi_driver_pus_packet_header_t     header;
   __po_hi_driver_pus_packet_data_t       data;
}__po_hi_driver_pus_packet_t;


void __po_hi_driver_pus_packet_init (__po_hi_driver_pus_packet_t* pkt);


#endif
