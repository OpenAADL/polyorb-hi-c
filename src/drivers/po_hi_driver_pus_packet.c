/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2010-2014 ESA & ISAE.
 */


#include <po_hi_types.h>
#include <drivers/po_hi_driver_pus_packet.h>


void __po_hi_driver_pus_packet_init (__po_hi_driver_pus_packet_t* pkt)
{
   pkt.id.version = 0;
}

__po_hi_driver_pus_packet_error_t __po_hi_driver_pus_packet_check (__po_hi_driver_pus_packet_t* pkt)
{
      if ((pkt.header.id.type == PO_HI_DRIVER_PUS_PACKET_TYPE_TC) && (pkt.header.id.flag == 0))
      {
         return __PO_HI_DRIVER_PUS_PACKET_ERROR_FLAG;
      }

      if (pkg.header.id.version != 0)
      {
         return __PO_HI_DRIVER_PUS_PACKET_ERROR_VERSION;
      }


      if (pkg.data.header.ccsds_secondary_flag != 0)
      {
         return __PO_HI_DRIVER_PUS_PACKET_ERROR_DATA_CCSDS_FLAG;
      }

   return __PO_HI_DRIVER_PUS_PACKET_ERROR_NO_ERROR;
}
