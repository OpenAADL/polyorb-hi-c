/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * Copyright (C) 2011, European Space Agency
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

