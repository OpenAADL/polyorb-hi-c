/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * Copyright (C) 2010, European Space Agency
 */

#include <deployment.h>

#ifndef __PO_HI_DRIVER_LINUX_SERIAL_H__
#define __PO_HI_DRIVER_LINUX_SERIAL_H__

#ifdef __PO_HI_NEED_DRIVER_SERIAL_LINUX

void __po_hi_c_driver_serial_linux_poller (void);

void __po_hi_c_driver_serial_linux_init (void);

int  __po_hi_c_driver_serial_linux_sender (__po_hi_task_id task, __po_hi_port_t port);

#endif

#endif

