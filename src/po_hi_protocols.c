/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2008, GET-Telecom Paris.
 */

#include <po_hi_config.h>
#include <po_hi_transport.h>
#include <po_hi_protocols.h>

int __po_hi_protocols_send (__po_hi_entity_t from,
			    __po_hi_entity_t to,
			    __po_hi_msg_t* msg)
{
  return (__po_hi_transport_send (from, to, msg));
}
