/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * Copyright (C) 2011, European Space Agency
 */

#include <deployment.h>
/* Generated code header */

#ifdef __PO_HI_NEED_DRIVER_SPACEWIRE_USB_BRICK

#include <activity.h>
#include <marshallers.h>
#include <deployment.h>

#include <po_hi_debug.h>
#include <po_hi_transport.h>
#include <po_hi_gqueue.h>
#include <po_hi_messages.h>
#include <po_hi_returns.h>

#include <drivers/po_hi_driver_usbbrick_spacewire.h>

#include <stdlib.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>
/* POSIX-style files */


void __po_hi_c_driver_spw_usb_brick_poller (const __po_hi_device_id dev_id)
{
}

void __po_hi_c_driver_spw_usb_brick_init (__po_hi_device_id id)
{
}

int __po_hi_c_driver_spw_usb_brick_sender (const __po_hi_task_id task_id, const __po_hi_port_t port)
{
   return 0;
}



#endif /*  __PO_HI_DRIVER_USBBRICK_SPACEWIRE_H__ */


