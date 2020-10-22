/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://www.openaadl.org
 *
 * Copyright (C) 2018-2019 ESA & ISAE, 2019-2020 OpenAADL
 */

#include <deployment.h>
/* Generated code header */

#include <string.h> /* for memcpy */
#include <signal.h>

#include <activity.h>
#include <marshallers.h>
#include <deployment.h>

#include <po_hi_debug.h>
#include <po_hi_transport.h>
#include <po_hi_gqueue.h>
#include <po_hi_messages.h>
#include <po_hi_returns.h>

#include <star_dundee_api.h>

__po_hi_request_t    __po_hi_c_driver_stardundee_request;
__po_hi_msg_t        __po_hi_c_driver_stardundee_poller_msg;
int                  po_hi_c_driver_stardundee_fd[__PO_HI_NB_DEVICES];
char                 __po_hi_c_driver_stardundee_sndbuf[__PO_HI_MESSAGES_MAX_SIZE + 1];
  STAR_CHANNEL_ID selectedChannel;

int isChannelValid(STAR_DEVICE_ID device, unsigned int channel);

/*****************************************************************************/
/* The StarDundee API requires all channels to be closed on exit, this
   signal handler performs the required clean-up */

void __po_hi_c_driver_stardundee_exit(int ignore) {
    (void)STAR_closeChannel(selectedChannel);
    __PO_HI_DEBUG_DEBUG ("Closing channel %d\n", selectedChannel);
    exit (0);
    return NULL;
}

/*****************************************************************************/
/* Body of the poller task */

void __po_hi_c_driver_stardundee_poller (const __po_hi_device_id dev_id) {
  int len;
  int ts;

  while (true) {
    __PO_HI_DEBUG_DEBUG ("[STAR DUNDEE MK3] Poller task activated \n");

    /* Prepare the message for reading */

    __po_hi_msg_reallocate (&__po_hi_c_driver_stardundee_poller_msg);

    /* Call Stardundee driver wrapper */

    len = dundee_receiving
      (&__po_hi_c_driver_stardundee_poller_msg.content[0],
       selectedChannel);

    __PO_HI_DEBUG_DEBUG
      ("[STAR DUNDEE MK3] Poller received a message, len=%d\n", len);

    if (len <= 0) {
      __PO_HI_DEBUG_CRITICAL ("[STAR DUNDEE MK3] Error while reading\n");

    } else {

#if __PO_HI_DEBUG_LEVEL >= __PO_HI_DEBUG_LEVEL_DEBUG
      __PO_HI_DEBUG_DEBUG ("Message content: |0x");
      for (ts = 0 ; ts < __PO_HI_MESSAGES_MAX_SIZE ; ts++) {
        __PO_HI_DEBUG_DEBUG
          ("%x", __po_hi_c_driver_stardundee_poller_msg.content[ts]);
      }
      __PO_HI_DEBUG_DEBUG ("|\n");
#endif

      /* Unmarshall request and do the upcall to the receiving thread */

      __po_hi_c_driver_stardundee_poller_msg.length = __PO_HI_MESSAGES_MAX_SIZE;
      __po_hi_unmarshall_request (&__po_hi_c_driver_stardundee_request,
                                  &__po_hi_c_driver_stardundee_poller_msg);

      __PO_HI_DEBUG_DEBUG ("[STAR DUNDEE MK3] Destination port: %d\n",
                           __po_hi_c_driver_stardundee_request.port);

      __po_hi_main_deliver (&__po_hi_c_driver_stardundee_request);
    }
  }
}

/*****************************************************************************/
/* Sender function */

__po_hi_msg_t           __po_hi_c_driver_stardundee_sender_msg;

int __po_hi_c_driver_stardundee_sender
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

   dev_id = __po_hi_get_device_from_port (port);

   if (dev_id == invalid_device_id) {
      __PO_HI_DEBUG_DEBUG("[STAR DUNDEE MK3] Invalid device id for sending\n");
      return __PO_HI_UNAVAILABLE;
   }

   local_port = __po_hi_get_local_port_from_global_port (port);

   request = __po_hi_gqueue_get_most_recent_value (task_id, local_port);

   if (request->port == -1) {
      __PO_HI_DEBUG_DEBUG
        ("[STAR DUNDEE MK3] Send output task %d, port %d : no value to send\n",
         task_id, port);
      return __PO_HI_SUCCESS;
   }

   destination_port = __po_hi_gqueue_get_destination (task_id, local_port, 0);

   __po_hi_msg_reallocate (&__po_hi_c_driver_stardundee_sender_msg);

   request->port = destination_port;

   sender_conf = (__po_hi_c_spacewire_conf_t*)
     __po_hi_get_device_configuration (dev_id);

   receiver_conf = (__po_hi_c_spacewire_conf_t*)
     __po_hi_get_device_configuration
     (__po_hi_get_device_from_port (destination_port));

   __po_hi_marshall_request
     (request, &__po_hi_c_driver_stardundee_sender_msg);

   len = -1;

#if __PO_HI_DEBUG_LEVEL >= __PO_HI_DEBUG_LEVEL_DEBUG
   __PO_HI_DEBUG_DEBUG ("Message content: |0x");
   for (ts = 0 ; ts < __PO_HI_MESSAGES_MAX_SIZE ; ts++) {
     __PO_HI_DEBUG_DEBUG
       ("%x", __po_hi_c_driver_stardundee_sender_msg.content[ts]);
   }
   __PO_HI_DEBUG_DEBUG ("|\n");
#endif

   len = dundee_sending
     (__po_hi_c_driver_stardundee_sender_msg.content,
      __PO_HI_MESSAGES_MAX_SIZE, // XXX hard coded
      selectedChannel); // XXX hard coded

   if (len < 0) {
      __PO_HI_DEBUG_CRITICAL (" [STAR DUNDEE MK3] failed !\n");
   } else
     if((0 <= len)&(len < __PO_HI_MESSAGES_MAX_SIZE)) {
      __PO_HI_DEBUG_CRITICAL (" [STAR DUNDEE MK3] Unable write !\n");
     } else {
       __PO_HI_DEBUG_DEBUG (" [STAR DUNDEE MK3] Send OK !\n");
   }

   request->port = __PO_HI_GQUEUE_INVALID_PORT;

   return __PO_HI_SUCCESS;
}

/******************************************************************************/
/* Driver initialization function */

void __po_hi_c_driver_stardundee_init (__po_hi_device_id id)
{
   unsigned int node_addr;
   __po_hi_c_spacewire_conf_t* drv_conf;

   /* Set sending callback function */

   __po_hi_transport_set_sending_func
     (id, __po_hi_c_driver_stardundee_sender);

   /* Set up current node address */

   drv_conf = (__po_hi_c_spacewire_conf_t*)
     __po_hi_get_device_configuration (id);
   node_addr = drv_conf->nodeaddr;

   __PO_HI_DEBUG_INFO ("[STAR DUNDEE MK3] Init, node address=%d\n", node_addr);

   /* Setting up SpaceWire device */

   __PO_HI_DEBUG_DEBUG ("[STAR DUNDEE MK3] Initializing driver \n");

  STAR_DEVICE_ID selectedDevice;
  unsigned char channel_number;
  U32 deviceCount = 0;
  STAR_DEVICE_ID * devices = STAR_getDeviceList(&deviceCount);
  selectedDevice = devices[0]; /* Here, we assume we have only one Star Dundee device */
  STAR_destroyDeviceList(devices);

  /** Finding the Channel_ID **/

  if(!isChannelValid(selectedDevice, node_addr)){
     __PO_HI_DEBUG_CRITICAL
       ("[STAR DUNDEE MK3] Invalid channel number for the poller\n");
     exit (0);
     return;
  }
  channel_number = (unsigned char) node_addr;

  STAR_CHANNEL_DIRECTION channelDirection = STAR_CHANNEL_DIRECTION_INOUT;
  selectedChannel = STAR_openChannelToLocalDevice
    (selectedDevice, channelDirection,
     (unsigned char)* &channel_number, 1);

  __PO_HI_DEBUG_DEBUG("node_addr = %d, channel_number= %d, channel_id= %d\n",
                      node_addr, channel_number,selectedChannel);

  if(selectedChannel==0){
    __PO_HI_DEBUG_CRITICAL
      ("[STAR DUNDEE MK3] Channel %d could not be opened FOR POLLER.\n",
       node_addr);
    exit (0);
    return;
  }

  /* Register clean-up function */
  signal (SIGKILL, __po_hi_c_driver_stardundee_exit);
  signal (SIGINT, __po_hi_c_driver_stardundee_exit);

   __PO_HI_DEBUG_DEBUG
     ("[STAR DUNDEE MK3] Initialization complete\n");
}

/******************************************************************************/
int isChannelValid(STAR_DEVICE_ID device, unsigned int channel){
  /* Get available channels */
  U32 channelMask = STAR_getDeviceChannels(device);

  /* Define counter for loop */
  unsigned int index;

  /* For all possible channels (apart from port 0) */
  for (index = 1; index < 32; index++)
    {
      /* If the channel exists */
      if ((channelMask >> index) & 1)
        {
          /* If this is the channel that we are looking for */
          if(index == channel)
            {
              /* Return true */
              return 1;
            }
        }
    }
    /* Return false if channel is invalid */
  return 0;
}
