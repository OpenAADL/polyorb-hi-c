/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2009, GET-Telecom Paris.
 */

#include <po_hi_returns.h>

#include <deployment.h>
#include <activity.h>

/*
 * This files provides a dummy implementation of low level transport,
 * for nodes that do not require transport.  
 */

void __po_hi_initialize_transport_low_level ()
{
}

int __po_hi_transport_low_level_send (__po_hi_entity_t from, 
				      __po_hi_entity_t to, 
				      __po_hi_msg_t* msg)
{
    return __PO_HI_SUCCESS;
}
