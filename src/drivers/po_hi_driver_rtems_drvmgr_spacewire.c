/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2018 ESA & ISAE.
 */

#include <deployment.h>
/* Generated code header */

#include <string.h> // for memcpy
#include <activity.h>
#include <marshallers.h>
#include <deployment.h>

#include <po_hi_debug.h>
#include <po_hi_transport.h>
#include <po_hi_gqueue.h>
#include <po_hi_messages.h>
#include <po_hi_returns.h>

#include <po_hi_driver_drvmgr_common.h>
/* Common drvmgr initialization */

#include <stdlib.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
/* POSIX-style files */

#include <grspw_api.h>

__po_hi_request_t    __po_hi_c_driver_drvmgr_grspw_request;
__po_hi_msg_t        __po_hi_c_driver_drvmgr_grspw_poller_msg;
int                  po_hi_c_driver_drvmgr_grspw_fd[__PO_HI_NB_DEVICES];
char                 __po_hi_c_driver_drvmgr_grspw_sndbuf[__PO_HI_MESSAGES_MAX_SIZE + 1];

/*****************************************************************************/
/* Body of the poller task */

void __po_hi_c_driver_drvmgr_grspw_poller (const __po_hi_device_id dev_id) {
  int len;
  int ts;

  while (true) {
    __PO_HI_DEBUG_DEBUG ("[GRSPW SPACEWIRE] Poller task activated \n");

    /* Prepare the message for reading */

    __po_hi_msg_reallocate (&__po_hi_c_driver_drvmgr_grspw_poller_msg);

    /* Call GRSPW driver wrapper */

    len = grspw_receiving
      (1, // XXX Hardcoded value for receiving
       &__po_hi_c_driver_drvmgr_grspw_poller_msg.content[0]);

    __PO_HI_DEBUG_DEBUG
      ("[GRSPW SPACEWIRE] Poller received a message, len=%d\n", len);

    if (len <= 0) {
      __PO_HI_DEBUG_CRITICAL ("[GRSPW SPACEWIRE] Error while reading\n");

    } else {

#if __PO_HI_DEBUG_LEVEL >= __PO_HI_DEBUG_LEVEL_DEBUG
      __PO_HI_DEBUG_DEBUG ("Message content: |0x");
      for (ts = 0 ; ts < __PO_HI_MESSAGES_MAX_SIZE ; ts++) {
        __PO_HI_DEBUG_DEBUG
          ("%x", __po_hi_c_driver_drvmgr_grspw_poller_msg.content[ts]);
      }
      __PO_HI_DEBUG_DEBUG ("|\n");
#endif

      /* Unmarshall request and do the upcall to the receiving thread */

      __po_hi_c_driver_drvmgr_grspw_poller_msg.length = __PO_HI_MESSAGES_MAX_SIZE;
      __po_hi_unmarshall_request (&__po_hi_c_driver_drvmgr_grspw_request,
                                  &__po_hi_c_driver_drvmgr_grspw_poller_msg);

      __PO_HI_DEBUG_DEBUG ("[GRSPW SPACEWIRE] Destination port: %d\n",
                           __po_hi_c_driver_drvmgr_grspw_request.port);

      __po_hi_main_deliver (&__po_hi_c_driver_drvmgr_grspw_request);
    }
  }
}

/******************************************************************************/
/* Sender function */

__po_hi_msg_t           __po_hi_c_driver_drvmgr_grspw_sender_msg;

int __po_hi_c_driver_drvmgr_grspw_sender
(const __po_hi_task_id task_id,
 const __po_hi_port_t port)
{
   int len = -1;
   int i;
   int ts;

   __po_hi_c_spacewire_conf_t* sender_conf;
   __po_hi_c_spacewire_conf_t* receiver_conf;

   __po_hi_local_port_t    local_port;
   __po_hi_request_t*      request;
   __po_hi_port_t          destination_port;

   __po_hi_device_id       dev_id;

   struct route_entry route; /* Routing table */

   dev_id = __po_hi_get_device_from_port (port);

   if (dev_id == invalid_device_id) {
      __PO_HI_DEBUG_DEBUG ("[RASTA SPW] Invalid device id for sending\n");
      return __PO_HI_UNAVAILABLE;
   }

   local_port = __po_hi_get_local_port_from_global_port (port);

   request = __po_hi_gqueue_get_most_recent_value (task_id, local_port);

   if (request->port == -1) {
      __PO_HI_DEBUG_DEBUG
        ("[GRSPW SPACEWIRE] Send output task %d, port %d : no value to send\n",
         task_id, port);
      return __PO_HI_SUCCESS;
   }

   destination_port = __po_hi_gqueue_get_destination (task_id, local_port, 0);

   __po_hi_msg_reallocate (&__po_hi_c_driver_drvmgr_grspw_sender_msg);

   request->port = destination_port;

   sender_conf = (__po_hi_c_spacewire_conf_t*)
     __po_hi_get_device_configuration (dev_id);

   receiver_conf = (__po_hi_c_spacewire_conf_t*)
     __po_hi_get_device_configuration
     (__po_hi_get_device_from_port (destination_port));

   __po_hi_marshall_request
     (request, &__po_hi_c_driver_drvmgr_grspw_sender_msg);

   len = -1;

   memset(&route, 0, sizeof(route));
   route.dstadr[0]= 1;

#if __PO_HI_DEBUG_LEVEL >= __PO_HI_DEBUG_LEVEL_DEBUG
      __PO_HI_DEBUG_DEBUG ("Message content: |0x");
      for (ts = 0 ; ts < __PO_HI_MESSAGES_MAX_SIZE ; ts++) {
        __PO_HI_DEBUG_DEBUG
          ("%x", __po_hi_c_driver_drvmgr_grspw_sender_msg.content[ts]);
      }
      __PO_HI_DEBUG_DEBUG ("|\n");
#endif

   len = grspw_sending
     (0, // XXX hardcoded
      &route,
      __po_hi_c_driver_drvmgr_grspw_sender_msg.content,
      __PO_HI_MESSAGES_MAX_SIZE);

   if (len < 0) {
      __PO_HI_DEBUG_CRITICAL (" [GRSPW SPACEWIRE] failed !\n");
   } else
     if((0 <= len)&(len < __PO_HI_MESSAGES_MAX_SIZE)) {
      __PO_HI_DEBUG_CRITICAL (" [GRSPW SPACEWIRE] Unable write !\n");
     } else {
       __PO_HI_DEBUG_DEBUG (" [GRSPW SPACEWIRE] Send OK !\n");
   }

   request->port = __PO_HI_GQUEUE_INVALID_PORT;

   return __PO_HI_SUCCESS;
}

/******************************************************************************/
/* Driver initialization function */

void __po_hi_c_driver_drvmgr_grspw_init (__po_hi_device_id id)
{
   unsigned int node_addr;
   __po_hi_c_spacewire_conf_t* drv_conf;

   /* Initializes drvmgr subsystem */

   __po_hi_c_driver_drvmgr_init ();

   /* Set sending callback function */

   __po_hi_transport_set_sending_func
     (id, __po_hi_c_driver_drvmgr_grspw_sender);

   /* Set up current node address */

   drv_conf = (__po_hi_c_spacewire_conf_t*)
     __po_hi_get_device_configuration (id);
   node_addr = drv_conf->nodeaddr;

   __PO_HI_DEBUG_INFO ("[GRSPW SPACEWIRE] Init, node address=%d\n", node_addr);

   /* Setting up SpaceWire device */

   __PO_HI_DEBUG_DEBUG ("[GRSPW SPACEWIRE] Initializing GRSPW driver \n");

   grspw_api_init();
   // XXX should also configure node address !

   __PO_HI_DEBUG_DEBUG
     ("[GRSPW SPACEWIRE] Initialization complete\n");

}
