/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * Copyright (C) 2010, European Space Agency
 */

#include <deployment.h>

#ifndef __PO_HI_DRIVER_RASTA_1553_H__
#define __PO_HI_DRIVER_RASTA_1553_H__

#ifdef __PO_HI_NEED_DRIVER_1553_RASTA

#include <drivers/po_hi_driver_rasta_1553_brmlib.h>

void  __po_hi_c_driver_1553_rasta_poller (void);

void  __po_hi_c_driver_1553_rasta_init (__po_hi_device_id id);

int   __po_hi_c_driver_1553_rasta_sender (const __po_hi_task_id task_id, const __po_hi_port_t port);

void  __po_hi_c_driver_1553_rasta_controller ();

int   __po_hi_c_driver_1553_rasta_proccess_list (__po_hi_c_driver_rasta_1553_brm_t chan, struct bc_msg *list, int test);

#endif

#endif

