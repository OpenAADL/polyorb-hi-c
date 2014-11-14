/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2010-2014 ESA & ISAE.
 */

#include <deployment.h>

#ifndef __PO_HI_DRIVER_LINUX_SERIAL_H__
#define __PO_HI_DRIVER_LINUX_SERIAL_H__

#if defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX_SENDER)

void __po_hi_c_driver_serial_linux_poller (const __po_hi_device_id dev_id);

void __po_hi_c_driver_serial_linux_init (__po_hi_device_id id);

int  __po_hi_c_driver_serial_linux_sender (__po_hi_task_id task, __po_hi_port_t port);

#endif

#endif
