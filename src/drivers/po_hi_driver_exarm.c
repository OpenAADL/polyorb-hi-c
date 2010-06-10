/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2010, European Space Agency
 * Copyright (C) 2007-2008, GET-Telecom Paris.
 */

#include <deployment.h>
#include <marshallers.h>

#ifdef __PO_HI_NEED_DRIVER_EXARM

#include <po_hi_config.h>
#include <po_hi_task.h>
#include <po_hi_transport.h>
#include <po_hi_debug.h>
#include <po_hi_types.h>
#include <po_hi_messages.h>
#include <po_hi_returns.h>
#include <po_hi_main.h>
#include <po_hi_task.h>
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

   __DEBUGMSG ("[DRIVER EXARM] Send to addr %s, port %d\n", __po_hi_driver_exarm_addr_to_send, __po_hi_driver_exarm_port_to_send);

   if ((__po_hi_driver_exarm_socket =socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP))==-1)
   {
      __DEBUGMSG ("[DRIVER EXARM] Cannot create UDP socket (device-id=%d)\n", id);
      return;
   }

   memset((char *) &__po_hi_driver_exarm_sin, 0, __po_hi_driver_exarm_slen);
   __po_hi_driver_exarm_sin.sin_family = AF_INET;
   __po_hi_driver_exarm_sin.sin_port = htons (__po_hi_driver_exarm_port_to_send);
   if (inet_aton (__po_hi_driver_exarm_addr_to_send, &__po_hi_driver_exarm_sin.sin_addr) == 0) 
   {
      __DEBUGMSG ("[DRIVER EXARM] inet_aton() failed (device-id=%d)\n", id);
      return;
   }
}

int  __po_hi_driver_exarm_send (__po_hi_entity_t from, __po_hi_entity_t to, __po_hi_msg_t* msg)
{
   int size_to_write;

   size_to_write = __PO_HI_MESSAGES_MAX_SIZE;

   if (sendto(__po_hi_driver_exarm_socket, &(msg->content), size_to_write, 0, (const struct sockaddr*)&__po_hi_driver_exarm_sin, __po_hi_driver_exarm_slen)==-1)
   {
      __DEBUGMSG ("[DRIVER EXARM] sendto() failed\n");
      perror ("error");
      return -1;
   }

   return 0;
}
#endif

