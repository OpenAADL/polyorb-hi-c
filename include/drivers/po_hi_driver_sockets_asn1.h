/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2010, European Space Agency
 */


#ifndef __PO_HI_DRIVER_SOCKETS_ASN1_H__
#define __PO_HI_DRIVER_SOCKETS_ASN1_H__

#include <deployment.h>

#ifdef __PO_HI_NEED_DRIVER_SOCKETS_ASN1

#include <po_hi_messages.h>

int __po_hi_driver_sockets_asn1_send (__po_hi_entity_t from, 
                                      __po_hi_entity_t to, 
                                      __po_hi_msg_t* msg);


void* __po_hi_sockets_asn1_poller (void);

void __po_hi_driver_sockets_receiver (void);

#endif /* __PO_HI_NEED_DRIVER_SOCKETS_ASN1 */

#endif /* __PO_HI_DRIVER_SOCKETS_ASN1_H__ */

