/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * Copyright (C) 2010, European Space Agency
 */

#include <deployment.h>

#ifdef __PO_HI_NEED_DRIVER_GENERIC_KEYBOARD

#include <po_hi_debug.h>

void __po_hi_driver_generic_keyboard_poller (void)
{
   __DEBUGMSG ("POLL THE KEYBOARD\n");
}

void __po_hi_driver_generic_keyboard_init (__po_hi_device_id id)
{
   __DEBUGMSG ("INIT KEYBOARD\n");
}

#endif

