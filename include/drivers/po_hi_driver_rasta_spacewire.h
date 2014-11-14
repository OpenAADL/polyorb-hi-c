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

#include <drivers/configuration/spacewire.h>

#ifndef __PO_HI_DRIVER_RASTA_SPACEWIRE_H__
#define __PO_HI_DRIVER_RASTA_SPACEWIRE_H__

#ifdef __PO_HI_NEED_DRIVER_SPACEWIRE_RASTA

void __po_hi_c_driver_spacewire_rasta_poller (const __po_hi_device_id dev_id);

void __po_hi_c_driver_spacewire_rasta_init (__po_hi_device_id id);

int __po_hi_c_driver_spacewire_rasta_sender (const __po_hi_task_id task_id, const __po_hi_port_t port);

#endif

#endif
