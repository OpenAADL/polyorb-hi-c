/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2011, European Space Agency (ESA).
 */

#include <deployment.h>

#if defined (__PO_HI_NEED_DRIVER_ETH_LEON) || \
    defined (__PO_HI_NEED_DRIVER_ETH_LEON_SENDER) || \
    defined (__PO_HI_NEED_DRIVER_ETH_LEON_RECEIVER)

#include <po_hi_debug.h>
#include <po_hi_utils.h>
#include <po_hi_messages.h>
#include <po_hi_transport.h>
#include <po_hi_gqueue.h>
#include <drivers/configuration/ip.h>
/* po-hi-c related files */

#include <activity.h>
#include <marshallers.h>
#include <deployment.h>
/* generated files */

#include <termios.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>

int po_hi_c_driver_leon_eth_fd_read;
int po_hi_c_driver_leon_eth_fd_write;

#if defined (__PO_HI_NEED_DRIVER_ETH_LEON) || \
    defined (__PO_HI_NEED_DRIVER_ETH_LEON_RECEIVER)

void __po_hi_c_driver_eth_leon_poller (const __po_hi_device_id dev_id)
{
   int n;
   int ts;
   int tr;

   (void) dev_id;

   __po_hi_msg_t msg;
   __po_hi_request_t request;

   __PO_HI_DEBUG_DEBUG ("[LEON ETH] Hello, i'm the eth poller , must read %d bytes on %d !\n", __PO_HI_MESSAGES_MAX_SIZE, po_hi_c_driver_leon_eth_fd_read);

   __po_hi_msg_reallocate (&msg);

   tr = 0;
   while (tr < __PO_HI_MESSAGES_MAX_SIZE)
   {
      if (read (po_hi_c_driver_leon_eth_fd_read, &(msg.content[tr]), 1) == 1)
      {
         tr++;
      }
   }

   msg.length = __PO_HI_MESSAGES_MAX_SIZE;
  __PO_HI_DEBUG_DEBUG ("[LEON ETH] read() syscall returns in total %d, received: ", tr);
#ifdef __PO_HI_DEBUG_DEBUG
   __PO_HI_DEBUG_DEBUG("[LEON ETH] Message received: 0x");
   for (ts = 0 ; ts < msg.length ; ts++)
   {
        __PO_HI_DEBUG_DEBUG ("%x", msg.content[ts]);
   }
   __PO_HI_DEBUG_DEBUG ("\n");
#endif

   __po_hi_unmarshall_request (&request, &msg);

   if (request.port > __PO_HI_NB_PORTS)
   {
      __PO_HI_DEBUG_WARNING ("[LEON ETH] Invalid port number !\n");
      return;
   }

   __PO_HI_DEBUG_INFO ("[LEON ETH] Destination port: %d\n", request.port);
   __po_hi_main_deliver (&request);
}
#endif

#if (defined (__PO_HI_NEED_DRIVER_ETH_LEON) || \
     defined (__PO_HI_NEED_DRIVER_ETH_LEON_SENDER))

void __po_hi_c_driver_eth_leon_init (__po_hi_device_id id)
{
}
#endif


#if defined (__PO_HI_NEED_DRIVER_ETH_LEON) 

int  __po_hi_c_driver_eth_leon_sender (__po_hi_task_id task, __po_hi_port_t port)
{
   int n;
   int ts;
   __po_hi_local_port_t local_port;
   __po_hi_request_t* request;
   __po_hi_msg_t msg;
   __po_hi_port_t destination_port;

   local_port = __po_hi_get_local_port_from_global_port (port);

   request = __po_hi_gqueue_get_most_recent_value (task, local_port);

   destination_port     = __po_hi_gqueue_get_destination (task, local_port, 0);

   __po_hi_msg_reallocate (&msg);

   request->port = destination_port;

   __po_hi_marshall_request (request, &msg);

   n = write (po_hi_c_driver_leon_eth_fd_write, &(msg.content[0]), __PO_HI_MESSAGES_MAX_SIZE);

#ifdef __PO_HI_DEBUG_INFO
   __PO_HI_DEBUG_INFO  ("[LEON ETH] Message sent: 0x");

   for (ts = 0 ; ts < __PO_HI_MESSAGES_MAX_SIZE ; ts++)
   {
      __PO_HI_DEBUG_INFO ("%x", msg.content[ts]);
   }
   __PO_HI_DEBUG_INFO ("\n");
#endif

   return 1;
}
#endif

#endif
