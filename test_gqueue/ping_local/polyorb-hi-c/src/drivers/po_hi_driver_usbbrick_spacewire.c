/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2011-2014 ESA & ISAE.
 */

#include <deployment.h>
/* Generated code header */

#ifdef __PO_HI_NEED_DRIVER_SPACEWIRE_USB_BRICK

#include <activity.h>
#include <marshallers.h>
#include <deployment.h>

#include <po_hi_debug.h>
#include <po_hi_transport.h>
#include <po_hi_gqueue.h>
#include <po_hi_messages.h>
#include <po_hi_returns.h>

#include <drivers/po_hi_driver_usbbrick_spacewire.h>

#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>
/* POSIX-style files */

#include "star_dundee_types.h"

#define SPW_MAX_PACKET_SIZE     8192
#define SPW_SEND_PACKET_SIZE    512

int                  __po_hi_c_driver_usb_brick_fd[__PO_HI_NB_DEVICES];
int                  __po_hi_c_driver_usb_brick_port[__PO_HI_NB_DEVICES];
star_device_handle   __po_hi_c_driver_usb_brick_star_device[__PO_HI_NB_DEVICES];

int __po_hi_driver_usbbrick_spw_init  (star_device_handle *phDevice,   /* Pointer to device handler */
                                       unsigned char num,              /* Device id to init */
                                       U32 frequency,
                                       U32 divider      /* frequency and divider */
)
{
        /* Open the SpaceWire device */
        if (!USBSpaceWire_Open(phDevice, num)) 
        {
                return 0xffffffff;
        }

        /* Get header mode for restoring at closure */
        if (USBSpaceWire_IsHeaderModeEnabled(*phDevice)) 
        {
                USBSpaceWire_EnableHeaderMode(phDevice, 0);
        }

        /* Get network mode for restoring at closure */
        if (USBSpaceWire_IsNetworkModeEnabled(*phDevice)) 
        {
                USBSpaceWire_EnableNetworkMode(*phDevice, 0);
        }

        /* Device must be RMAP for the following configuration */
        /* Mandatory configuration for StarDundee device: do not modify */
        CFGSpaceWire_EnableRMAP(1);
        CFGSpaceWire_SetRMAPDestinationKey(0x20);
        CFGSpaceWire_AddrStackPush(0);
        CFGSpaceWire_AddrStackPush(254);
        CFGSpaceWire_RetAddrStackPush(254);

        /* Receive on all ports */
        USBSpaceWire_RegisterReceiveOnAllPorts(*phDevice);

        if (CFGSpaceWire_SetAsInterface(*phDevice, 1, 0) != CFG_TRANSFER_SUCCESS) 
        {
           __DEBUGMSG(stderr, "Couldn't set the device as an interface.\n");
        }

        /* Setting the speed */
        CFGSpaceWire_SetBrickBaseTransmitRate(*phDevice, frequency, divider, 0xff);

        return 0;
}

__po_hi_request_t __po_hi_c_driver_spw_usb_brick_request;
__po_hi_msg_t     __po_hi_c_driver_spw_usb_brick_poller_msg;

void __po_hi_c_driver_spw_usb_brick_poller (const __po_hi_device_id dev_id)
{
   int n;
   int ts;

   unsigned long* swap_pointer;
   unsigned long swap_value;

   USB_SPACEWIRE_STATUS status;
   USB_SPACEWIRE_PACKET_PROPERTIES props;
   USB_SPACEWIRE_EOP_TYPE eop;
   USB_SPACEWIRE_ID id;


   __PO_HI_DEBUG_DEBUG ("[USB-SPW] Hello, i'm the spacewire poller on the brick, must read %d bytes!\n", __PO_HI_MESSAGES_MAX_SIZE);

   __po_hi_msg_reallocate (&__po_hi_c_driver_spw_usb_brick_poller_msg);

   status = USBSpaceWire_ReadPackets(__po_hi_c_driver_usb_brick_star_device[dev_id], &__po_hi_c_driver_spw_usb_brick_poller_msg.content[0], __PO_HI_MESSAGES_MAX_SIZE, 1, 1, &props, &id);
   if (status != TRANSFER_SUCCESS)
   {
      __PO_HI_DEBUG_DEBUG ("[USB-SPW] Read error, status=%d!\n", status);
   }

   eop = props.eop;

   USBSpaceWire_FreeRead(__po_hi_c_driver_usb_brick_star_device[dev_id], id);

   n = props.len;

   if (n == -1)
   {
      __PO_HI_DEBUG_DEBUG ("[USB-SPẄ] Cannot read !\n");
      return;
   }

   if (n == 0)
   {
      return;
   }

   if (n != __PO_HI_MESSAGES_MAX_SIZE)
   {
      __PO_HI_DEBUG_CRITICAL ("[USB-SPW] Inconsistent received message size (received %d bytes)!\n", n);
      return;
   }

   __PO_HI_DEBUG_DEBUG ("[USB-SPW] read() on %d returns %d\n", __po_hi_c_driver_usb_brick_star_device[dev_id], n);



   __PO_HI_DEBUG_DEBUG  ("[USB-SPW] Message: 0x");

   for (ts = 0 ; ts < __PO_HI_MESSAGES_MAX_SIZE ; ts++)
   {
      __PO_HI_DEBUG_DEBUG ("%x", __po_hi_c_driver_spw_usb_brick_poller_msg.content[ts]);
   }
   __PO_HI_DEBUG_DEBUG ("\n");
   swap_pointer  = (unsigned long*) &__po_hi_c_driver_spw_usb_brick_poller_msg.content[0];
   swap_value    = *swap_pointer;
   *swap_pointer = __po_hi_swap_byte (swap_value);

   __po_hi_c_driver_spw_usb_brick_poller_msg.length = n;

   __PO_HI_DEBUG_DEBUG ("[USB-SPW] Message after swapped port: 0x");
   for (ts = 0 ; ts < __po_hi_c_driver_spw_usb_brick_poller_msg.length ; ts++)
   {
        __PO_HI_DEBUG_DEBUG ("%x", __po_hi_c_driver_spw_usb_brick_poller_msg.content[ts]);
   }
   __PO_HI_DEBUG_DEBUG ("\n");

   __PO_HI_DEBUG_DEBUG ("[USB-SPW] Received: %s\n", __po_hi_c_driver_spw_usb_brick_poller_msg.content);

   __po_hi_unmarshall_request (&__po_hi_c_driver_spw_usb_brick_request, &__po_hi_c_driver_spw_usb_brick_poller_msg);

   if (__po_hi_c_driver_spw_usb_brick_request.port > __PO_HI_NB_PORTS)
   {
      __PO_HI_DEBUG_DEBUG ("[USB-SPW] Invalid port number !\n");
      return;
   }

   __PO_HI_DEBUG_DEBUG ("[USB-SPW] Destination port: %d\n", __po_hi_c_driver_spw_usb_brick_request.port);
   __po_hi_main_deliver (&__po_hi_c_driver_spw_usb_brick_request);


}

void __po_hi_c_driver_spw_usb_brick_init (__po_hi_device_id id)
{
   int i;
   __po_hi_c_spacewire_conf_t* drv_conf;

   drv_conf = (__po_hi_c_spacewire_conf_t*) __po_hi_get_device_configuration (id);

   /* Get the first device connected */
   __po_hi_c_driver_usb_brick_fd[id]   = USBSpaceWire_ListDevices();


   __po_hi_transport_set_sending_func (id, __po_hi_c_driver_spw_usb_brick_sender);

   __po_hi_c_driver_usb_brick_port[id] = 1;
   if (strncmp (drv_conf->devname, "node2", 5) == 0)
   {
      __po_hi_c_driver_usb_brick_port[id] = 1;
   }

   for (i = 0; i < 32; i++) 
   {
      if (__po_hi_c_driver_usb_brick_fd[id] == (unsigned long)(1 << i)) 
      {
         __po_hi_c_driver_usb_brick_fd[id] = i;
         break;
      }
   }

   /* Initialize the device at 100 Mbps */
   if (__po_hi_driver_usbbrick_spw_init(&__po_hi_c_driver_usb_brick_star_device[id],__po_hi_c_driver_usb_brick_fd[id] , CFG_BRK_CLK_200_MHZ, CFG_BRK_DVDR_2) == -1) 
   {
      __PO_HI_DEBUG_DEBUG ("[USB-BRICK] SpaceWire device initialisation error.\n");
      return;
   }

   __PO_HI_DEBUG_DEBUG ("[USB-BRICK] SpaceWire device initialisation complete, fd=%d\n", __po_hi_c_driver_usb_brick_fd[id] );
}



__po_hi_msg_t           __po_hi_c_driver_spw_usb_brick_sender_msg;

int __po_hi_c_driver_spw_usb_brick_sender (const __po_hi_task_id task_id, const __po_hi_port_t port)
{
   int                     n;
   int                     ts;

   uint8_t buf[__PO_HI_MESSAGES_MAX_SIZE+1];

   unsigned long* swap_pointer;
   unsigned long swap_value;
   __po_hi_local_port_t    local_port;
   __po_hi_request_t*      request;
   __po_hi_port_t          destination_port;
   __po_hi_device_id       dev_id;

   USB_SPACEWIRE_STATUS    status;
   USB_SPACEWIRE_ID        id;

   dev_id = __po_hi_get_device_from_port (port);

   if (dev_id == invalid_device_id)
   {
      __PO_HI_DEBUG_DEBUG ("[USB-SPW] Invalid device id for sending\n");
      return __PO_HI_UNAVAILABLE;
   }

   local_port = __po_hi_get_local_port_from_global_port (port);

   request = __po_hi_gqueue_get_most_recent_value (task_id, local_port);

   if (request->port == -1)
   {
      __PO_HI_DEBUG_DEBUG ("[USB-SPW] Send output task %d, port %d (local_port=%d): no value to send\n", task_id, port, local_port);
      return __PO_HI_SUCCESS;
   }

   destination_port     = __po_hi_gqueue_get_destination (task_id, local_port, 0);

   __po_hi_msg_reallocate (&__po_hi_c_driver_spw_usb_brick_sender_msg);

   request->port = destination_port;
   __PO_HI_DEBUG_DEBUG ("[USB-SPW] Destination port= %d, send through device %d (fd=%d)\n", destination_port, dev_id, __po_hi_c_driver_usb_brick_fd[dev_id]);

   __po_hi_marshall_request (request, &__po_hi_c_driver_spw_usb_brick_sender_msg);
   swap_pointer  = (unsigned long*) &__po_hi_c_driver_spw_usb_brick_sender_msg.content[0];
   swap_value    = *swap_pointer;
   *swap_pointer = __po_hi_swap_byte (swap_value);

   buf[0] = __po_hi_c_driver_usb_brick_port[dev_id];

   __PO_HI_DEBUG_DEBUG ("[USB-SPW] write() send on port %d\n", __po_hi_c_driver_usb_brick_port[dev_id]);

   memcpy (&buf[1], __po_hi_c_driver_spw_usb_brick_sender_msg.content, __PO_HI_MESSAGES_MAX_SIZE);
   if ((status = USBSpaceWire_SendPacket(__po_hi_c_driver_usb_brick_star_device[dev_id], buf, __PO_HI_MESSAGES_MAX_SIZE + 1, 1, &id)) != TRANSFER_SUCCESS) 
   {
      __PO_HI_DEBUG_DEBUG("[USB-SPW] Write error: %d.\n", status);
      return 0;
   }

   __PO_HI_DEBUG_DEBUG ("Sent: |0x");
   for (ts = 0 ; ts < __PO_HI_MESSAGES_MAX_SIZE ; ts++)
   {
      __PO_HI_DEBUG_DEBUG ("%x", __po_hi_c_driver_spw_usb_brick_sender_msg.content[ts]);
   }
   __PO_HI_DEBUG_DEBUG ("|\n");


   USBSpaceWire_FreeSend (__po_hi_c_driver_usb_brick_star_device[dev_id], id);

   __PO_HI_DEBUG_DEBUG ("[USB-SPW] write() using star device %d returns %d\n", __po_hi_c_driver_usb_brick_star_device[dev_id - 1], status);

   request->port = __PO_HI_GQUEUE_INVALID_PORT;

   return 1;
}

#endif
