#include <stdio.h>
#include <deployment.h>
#include <po_hi_debug.h>
#include <po_hi_types.h>
#include <po_hi_transport.h>
#include <po_hi_gqueue.h>
#include <request.h>
#include <xm.h>

void user_ports_polling ()
{
   __po_hi_port_t portno;
   __po_hi_node_t mynode;
   __po_hi_node_t tmpnode;
   __po_hi_request_t request;
   __po_hi_port_kind_t pkind;
   int ret;
   
   mynode = __po_hi_transport_get_mynode ();

   for (portno = 0 ; portno < __PO_HI_NB_PORTS ; portno++)
   {
      pkind = __po_hi_transport_get_port_kind (portno);
      tmpnode = __po_hi_transport_get_node_from_entity (__po_hi_get_entity_from_global_port (portno));

      ret = -1;

      if (tmpnode == mynode)
      {

         if (pkind ==  __PO_HI_IN_DATA_INTER_PROCESS)
         {
             ret = XM_read_sampling_message (__po_hi_transport_xtratum_get_port (portno),
                                              &request,
                                              sizeof (__po_hi_request_t), 0);
           
         }

         if (pkind ==  __PO_HI_IN_EVENT_DATA_INTER_PROCESS)
         {
            ret = XM_receive_queuing_message (__po_hi_transport_xtratum_get_port (portno),
                                              &request,
                                              sizeof (__po_hi_request_t));
         }

         __DEBUGMSG ("[XTRATUM POLLER] Poll port %d, corresponding xtratum port = %d, return=%d\n", portno, __po_hi_transport_xtratum_get_port (portno), ret);

         if (ret > 0)
         {
            __po_hi_main_deliver (&request);
         }
      }
   }
}
