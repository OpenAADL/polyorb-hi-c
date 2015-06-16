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

#include <drivers/po_hi_driver_serial_common.h>
#include <drivers/configuration/serial.h>

#if defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX_RECEIVER) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX_SENDER) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_RASTA) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LEON) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LEON_SENDER) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LEON_RECEIVER)

#include <po_hi_transport.h>
#include <po_hi_debug.h>

int __po_hi_c_driver_serial_common_get_speed (const __po_hi_device_id id)
{
   __po_hi_c_serial_conf_t*   serialconf;
   
   serialconf = (__po_hi_c_serial_conf_t*)__po_hi_get_device_configuration (id);

   switch (serialconf->speed)
   {
      case __po_hi_c_b115200:
         __PO_HI_DEBUG_INFO ("Get speed 115200 for device %d\n", id);
         return __PO_HI_DRIVER_SERIAL_COMMON_SPEED_115200;
         break;

      case __po_hi_c_b57600:
         __PO_HI_DEBUG_INFO ("Get speed 57600 for device %d\n", id);
         return __PO_HI_DRIVER_SERIAL_COMMON_SPEED_57600;
         break;

      case __po_hi_c_b38400:
         __PO_HI_DEBUG_INFO ("Get speed 38400 for device %d\n", id);
         return __PO_HI_DRIVER_SERIAL_COMMON_SPEED_38400;
         break;

      case __po_hi_c_b19200:
         __PO_HI_DEBUG_INFO ("Get speed 19200 for device %d\n", id);
         return __PO_HI_DRIVER_SERIAL_COMMON_SPEED_19200;
         break;

      default:
         __PO_HI_DEBUG_INFO ("Unknown speed for device %d\n", id);
         return __PO_HI_DRIVER_SERIAL_COMMON_SPEED_UNKNWON;
         break;
   }

   return __PO_HI_DRIVER_SERIAL_COMMON_SPEED_DEFAULT;
}

#endif 
