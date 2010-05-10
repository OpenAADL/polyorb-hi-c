/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * Copyright (C) 2010, European Space Agency
 */

#include <deployment.h>

#ifndef __PO_HI_DRIVER_RASTA_SPACEWIRE_H__
#define __PO_HI_DRIVER_RASTA_SPACEWIRE_H__

#ifdef __PO_HI_NEED_DRIVER_SPACEWIRE_RASTA

#define __PO_HI_DRIVER_RASTA_SPACEWIRE_RXPKT_BUF   5

#define __PO_HI_DRIVER_RASTA_SPACEWIRE_PKTSIZE      1000

typedef struct {
   unsigned char addr;
   unsigned char protid;
   unsigned char dummy;
   unsigned char channel;
   unsigned char data[__PO_HI_DRIVER_RASTA_SPACEWIRE_PKTSIZE];
}__po_hi_c_driver_spacewire_pkt_hdr_t;

void __po_hi_c_driver_spacewire_rasta_poller (void);

void __po_hi_c_driver_spacewire_rasta_init (__po_hi_device_id id);

int __po_hi_c_driver_spacewire_rasta_sender (const __po_hi_task_id task_id, const __po_hi_port_t port);

#endif

#endif

