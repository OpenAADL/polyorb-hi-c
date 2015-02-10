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

#ifndef __PO_HI_DRIVER_SERIAL_COMMON_H__

#if defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX_RECEIVER) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX_SENDER) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_RASTA) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LEON) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LEON_SENDER) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LEON_RECEIVER)

#include <po_hi_debug.h>
#include <drivers/configuration/serial.h>

#define __PO_HI_DRIVER_SERIAL_COMMON_SPEED_19200    2
#define __PO_HI_DRIVER_SERIAL_COMMON_SPEED_38400    6
#define __PO_HI_DRIVER_SERIAL_COMMON_SPEED_57600    8
#define __PO_HI_DRIVER_SERIAL_COMMON_SPEED_115200  10
#define __PO_HI_DRIVER_SERIAL_COMMON_SPEED_UNKNWON  0

#define __PO_HI_DRIVER_SERIAL_COMMON_SPEED_DEFAULT  __PO_HI_DRIVER_SERIAL_COMMON_SPEED_38400

int __po_hi_c_driver_serial_common_get_speed (const __po_hi_device_id id);
/*
 * __po_hi_c_driver_serial_common_get_speed provides the speed
 * of the serial line associated with a serial driver.
 * Returns the speed of the port using a macro which
 * has the form __PO_HI_DRIVER_SERIAL_COMMON_SPEED_XXXXX (XXXX being the
 * potential speeds. If the parameter is not set on the device, it returns
 * __PO_HI_DRIVER_SERIAL_COMMON_SPEED_DEFAULT. If the configuration is not
 * valid, it returns __PO_HI_DRIVER_SERIAL_COMMON_SPEED_UNKNWON
 */

#endif 

#endif
