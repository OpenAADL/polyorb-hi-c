/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * Copyright (C) 2010, European Space Agency
 */

#include <deployment.h>

#ifndef __PO_HI_DRIVER_EXARM_H__
#define __PO_HI_DRIVER_EXARM_H__

#include <po_hi_transport.h>

#include <drivers/po_hi_driver_sockets_common.h>
/* Files from PolyORB-HI-C */

int  __po_hi_driver_exarm_send (__po_hi_entity_t from, __po_hi_entity_t to, __po_hi_msg_t* msg);
/*
 * Send data through the sending socket
 */

void __po_hi_driver_exarm_init (__po_hi_device_id id);
#endif

#endif

