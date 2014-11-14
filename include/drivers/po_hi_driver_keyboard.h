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

#ifndef __PO_HI_DRIVER_LINUX_KEYBOARD_H__
#define __PO_HI_DRIVER_LINUX_KEYBOARD_H__

#ifdef __PO_HI_NEED_DRIVER_GENERIC_KEYBOARD

void __po_hi_driver_generic_keyboard_poller (const __po_hi_device_id dev_id, int* key_pressed);

void __po_hi_driver_generic_keyboard_init (__po_hi_device_id id);

#endif

#endif
