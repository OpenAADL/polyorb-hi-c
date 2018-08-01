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

#include <star_dundee_api.h>

__po_hi_request_t    __po_hi_c_driver_stardundee_request;
__po_hi_msg_t        __po_hi_c_driver_stardundee_poller_msg;
int                  po_hi_c_driver_stardundee_fd[__PO_HI_NB_DEVICES];
char                 __po_hi_c_driver_stardundee_sndbuf[__PO_HI_MESSAGES_MAX_SIZE + 1];

/*****************************************************************************/
/* Body of the poller task */

void __po_hi_c_driver_stardundee_poller (const __po_hi_device_id dev_id) {
  int len;
  int ts;
  STAR_DEVICE_ID selectedDevice;
  STAR_CHANNEL_ID selectedChannel;
  unsigned char channel_number;
  unsigned int node_addr;
  /** Finding the Device_ID **/
 /* The number of devices that were found */
  U32 deviceCount = 0;
 /* TEST IF */
  STAR_DEVICE_ID * devices = STAR_getDeviceList(&deviceCount);
 if (dev_id >= deviceCount){
    printf("invalid device id for the poller\n");
 }
  selectedDevice = devices[dev_id];
  STAR_destroyDeviceList(devices);

  /** Finding the Channel_ID **/
  //STAR_CHANNEL_DIRECTION channelDirection = STAR_CHANNEL_DIRECTION_INOUT;
   __po_hi_c_spacewire_conf_t* drv_conf;
  drv_conf = (__po_hi_c_spacewire_conf_t*)
     __po_hi_get_device_configuration (dev_id);
  node_addr = drv_conf->nodeaddr;
  if(!isChannelValid(selectedDevice, node_addr)){
     printf("Invalid channel number for the poller\n");
     return PO_HI_ERROR;
  }
  channel_number = (unsigned char) node_addr;

  STAR_CHANNEL_DIRECTION channelDirection = STAR_CHANNEL_DIRECTION_IN;
  selectedChannel = STAR_openChannelToLocalDevice(selectedDevice, channelDirection,
        (unsigned char)* channelNumber, 1);
   printf("node_addr = %d, channel_number= %c, channel_id= %c\n",node_addr, channel_number,selectedChannel);
  if(selectedChannel==0){
    printf("Channel %d could not be opened FOR POLLER.\n", node_addr);
    return PO_HI_ERROR;
  }
  while (true) {
    __PO_HI_DEBUG_DEBUG ("[STAR DUNDEE MK3] Poller task activated \n");

    /* Prepare the message for reading */

    __po_hi_msg_reallocate (&__po_hi_c_driver_stardundee_poller_msg);

    /* Call Stardundee driver wrapper */

    len = dundee_receiving
      (&__po_hi_c_driver_stardundee_poller_msg.content[0],
       selectedChannel); // XXX hard coded

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
  (void)STAR_closeChannel(selectedChannel);
}

/******************************************************************************/
/* Sender function */

__po_hi_msg_t           __po_hi_c_driver_stardundee_sender_msg;

int __po_hi_c_driver_stardundee_sender
(const __po_hi_task_id task_id,
 const __po_hi_port_t port)
{
   int len = -1;
   int i;
   int ts;

   STAR_DEVICE_ID selectedDevice;
   STAR_CHANNEL_ID selectedChannel;
   unsigned char channel_number;
   unsigned int node_addr;
   /** Finding the Device_ID **/
   /* The number of devices that were found */
   U32 deviceCount = 0;
   /* Get the list of available SpaceWire devices */
   STAR_DEVICE_ID * devices = STAR_getDeviceList(&deviceCount);
   if (dev_id >= deviceCount){
     printf("invalid device id for the sender\n");
   }
   selectedDevice = devices[dev_id];
   STAR_destroyDeviceList(devices);

   /** Finding the Channel_ID **/
   //STAR_CHANNEL_DIRECTION channelDirection = STAR_CHANNEL_DIRECTION_INOUT;
   __po_hi_c_spacewire_conf_t* drv_conf;
   drv_conf = (__po_hi_c_spacewire_conf_t*)
     __po_hi_get_device_configuration (dev_id);
   node_addr = drv_conf->nodeaddr;

   if(!isChannelValid(selectedDevice, node_addr)){
     printf("Invalid channel number for the sender\n");
     return PO_HI_ERROR;
   }

   channel_number = (unsigned char) node_addr;
   STAR_CHANNEL_DIRECTION channelDirection = STAR_CHANNEL_DIRECTION_OUT;
   selectedChannel = STAR_openChannelToLocalDevice
     (selectedDevice, channelDirection,
      (unsigned char)* channelNumber,
      1);

   printf("node_addr = %d, channel_number= %c, channel_id= %c\n",node_addr, channel_number,selectedChannel);

   if(selectedChannel==0){
     printf("Channel %d could not be opened FOR SENDER.\n", node_addr);
     return PO_HI_ERROR;
   }
   __po_hi_c_spacewire_conf_t* sender_conf;
   __po_hi_c_spacewire_conf_t* receiver_conf;

   __po_hi_local_port_t    local_port;
   __po_hi_request_t*      request;
   __po_hi_port_t          destination_port;

   __po_hi_device_id       dev_id;

   dev_id = __po_hi_get_device_from_port (port);

   if (dev_id == invalid_device_id) {
      __PO_HI_DEBUG_DEBUG ("[RASTA SPW] Invalid device id for sending\n");
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
   (void)STAR_closeChannel(selectedChannel);
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

   /* Note: there is no init function for Star Dundee wrapper API */

   __PO_HI_DEBUG_DEBUG
     ("[STAR DUNDEE MK3] Initialization complete\n");
}

int isChannelValid(STAR_DEVICE_ID device, unsigned int channel){
  /* Get available channels */
  U32 channelMask = STAR_getDeviceChannels(device);

  printf("test :channel is : %d \n", channel);
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
