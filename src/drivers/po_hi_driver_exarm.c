/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2010-2014 ESA & ISAE.
 */

#include <deployment.h>

#ifdef __PO_HI_NEED_DRIVER_EXARM

#include <marshallers.h>
#include <po_hi_config.h>
#include <po_hi_task.h>
#include <po_hi_transport.h>
#include <po_hi_debug.h>
#include <po_hi_types.h>
#include <po_hi_messages.h>
#include <po_hi_returns.h>
#include <po_hi_main.h>
#include <po_hi_task.h>
#include <po_hi_gqueue.h>
#include <po_hi_utils.h>

#include <drivers/po_hi_driver_sockets.h>

#include <activity.h>

#include <signal.h>
#include <string.h>
#include <unistd.h>
#include <netdb.h>
#include <sys/types.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <sys/time.h>

char __po_hi_driver_exarm_addr_to_send[16];
int  __po_hi_driver_exarm_port_to_send;
struct sockaddr_in __po_hi_driver_exarm_sin;
int __po_hi_driver_exarm_socket;
int __po_hi_driver_exarm_slen;

void __po_hi_driver_exarm_init (__po_hi_device_id id)
{
   char* dev_conf;

   __po_hi_driver_exarm_slen = sizeof (__po_hi_driver_exarm_sin);

   dev_conf = __po_hi_get_device_naming (id);

   memset (__po_hi_driver_exarm_addr_to_send, '\0', 16);

   if (sscanf (dev_conf, "%s %d", __po_hi_driver_exarm_addr_to_send, &__po_hi_driver_exarm_port_to_send) == 0)
   {
      __DEBUGMSG ("[DRIVER EXARM] Unable to parse device configuration (device-id=%d)\n", id);
      return;
   }

   __DEBUGMSG ("[DRIVER EXARM] Send to addr [%s], port [%d]\n", __po_hi_driver_exarm_addr_to_send, __po_hi_driver_exarm_port_to_send);

   if ((__po_hi_driver_exarm_socket =socket(AF_INET, SOCK_DGRAM, 0))==-1)
   {
      __DEBUGMSG ("[DRIVER EXARM] Cannot create UDP socket (device-id=%d)\n", id);
      return;
   }

   memset (&__po_hi_driver_exarm_sin, 0, __po_hi_driver_exarm_slen);
   __po_hi_driver_exarm_sin.sin_family = AF_INET;
   __po_hi_driver_exarm_sin.sin_port = htons (__po_hi_driver_exarm_port_to_send);
   if (inet_aton (__po_hi_driver_exarm_addr_to_send, &__po_hi_driver_exarm_sin.sin_addr) == 0) 
   {
      __DEBUGMSG ("[DRIVER EXARM] inet_aton() failed (device-id=%d)\n", id);
      return;
   }
   __DEBUGMSG ("[DRIVER EXARM] Init done\n");
}

int __po_hi_driver_exarm_send (__po_hi_task_id task, __po_hi_port_t port)
{
   int                     size_to_write;
   __po_hi_local_port_t    local_port;
   __po_hi_request_t*      request;

   local_port = __po_hi_get_local_port_from_global_port (port);

   request = __po_hi_gqueue_get_most_recent_value (task, local_port);

   size_to_write = sizeof (request->vars);

#if 0
   {

      int                     i;
      uint32_t*               swap;
      swap = (uint32_t*) &(request->vars);
      for (i = 0 ; i < size_to_write / 4 ; i++)
      {
         __po_hi_swap_byte (*swap);
         swap++;
      }
   }
#endif

   int ret = sendto(__po_hi_driver_exarm_socket, &(request->vars), size_to_write, 0, (struct sockaddr*)&__po_hi_driver_exarm_sin, __po_hi_driver_exarm_slen);

   if(ret == -1)
   {
      __DEBUGMSG ("[DRIVER EXARM] sendto() failed\n");
      return -1;
   }

   if (ret != size_to_write)
   {
      __DEBUGMSG ("[DRIVER EXARM] sendto() inconsistend return, try to write %d, ret=%d\n", size_to_write, ret);
      return -1;
   }

   return 0;
}
#endif
