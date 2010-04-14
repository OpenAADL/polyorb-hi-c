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
#include <po_hi_types.h>
#include <po_hi_debug.h>
#include <po_hi_transport.h>
#include <po_hi_giop.h>
#include <po_hi_messages.h>
#include <po_hi_returns.h>

#include <deployment.h>
#include <activity.h>
#include <request.h>

/*
 * The following arrays are declared in the generated header
 * deployment.h.
 */

extern __po_hi_node_t 
entity_table[__PO_HI_NB_ENTITIES];

void __po_hi_initialize_transport ()
{
#if __PO_HI_NB_NODES > 1
  __po_hi_initialize_transport_low_level ();
#endif
}

int __po_hi_transport_send (__po_hi_entity_t from,
			    __po_hi_entity_t to,
			    __po_hi_msg_t* msg)
{
  if (entity_table[from] == entity_table[to])
    {
#ifdef __PO_HI_DEBUG
      __DEBUGMSG (" ... deliver locally ... \n");
#endif
      __po_hi_main_deliver(msg);
      return __PO_HI_SUCCESS;
    }
  else
    {      
#ifdef __PO_HI_USE_GIOP
      return __po_hi_giop_send (from, to, msg); 
#else
      return __po_hi_transport_low_level_send (from, to, msg); 
#endif
    }
}
