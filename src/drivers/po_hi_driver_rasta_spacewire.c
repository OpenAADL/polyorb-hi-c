/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * Copyright (C) 2010, European Space Agency
 */

#include <deployment.h>
/* Generated code header */

#ifdef __PO_HI_NEED_DRIVER_SPACEWIRE_RASTA

#include <activity.h>
#include <marshallers.h>
#include <deployment.h>

#include <po_hi_debug.h>
#include <po_hi_transport.h>
#include <po_hi_gqueue.h>
#include <po_hi_messages.h>
#include <drivers/po_hi_rtems_utils.h>
#include <drivers/po_hi_driver_rasta_spacewire.h>

#include <stdlib.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>
/* POSIX-style files */

#include <pci.h>
#include <rasta.h>
#include <grspw_rasta.h>
#include <apbuart_rasta.h>
/* Rasta includes from GAISLER drivers */

#define __PO_HI_DRIVER_SPACEWIRE_RASTA_DEVICE "/dev/grspwrasta0"

static unsigned char po_hi_c_driver_spacewire_rxpkt[__PO_HI_DRIVER_RASTA_SPACEWIRE_PKTSIZE * __PO_HI_DRIVER_RASTA_SPACEWIRE_RXPKT_BUF];
static __po_hi_c_driver_spacewire_pkt_hdr_t po_hi_c_driver_spacewire_txpkts[1];

int po_hi_c_driver_rasta_spacewire_fd;

void po_hi_c_driver_rasta_spacewire_init_pkt(__po_hi_c_driver_spacewire_pkt_hdr_t *p)
{
  p->addr = 10;  /* FIXME ! Need to retrieve that from the AADL model ! */
  p->protid = 50;
  p->dummy = 0x01;
  p->channel = 0x01;
  memset (p->data, '\0', __PO_HI_DRIVER_RASTA_SPACEWIRE_PKTSIZE);
}


void __po_hi_c_driver_spacewire_rasta_poller (void)
{
   int len;
   int j;

   __po_hi_msg_t msg;
   __po_hi_request_t request;

   __DEBUGMSG ("[RASTA SPACEWIRE] Hello, i'm the poller !\n");

   len = read (po_hi_c_driver_rasta_spacewire_fd,
               &po_hi_c_driver_spacewire_rxpkt[0],
               __PO_HI_DRIVER_RASTA_SPACEWIRE_PKTSIZE * __PO_HI_DRIVER_RASTA_SPACEWIRE_RXPKT_BUF);

   if (len < 0)
   {
      __DEBUGMSG ("[RASTA SPACEWIRE] Error while reading\n");
   }
   else
   {

      /* skip first 2bytes (vchan and dummy) */
      if ( (po_hi_c_driver_spacewire_rxpkt[0]==1) && (po_hi_c_driver_spacewire_rxpkt[1]==1) )
      {
         j=2; /* strip virtual channel protocol, non-ssspw device */
      }
      else
      {
         j=0; /* hardware uses virtual channel protocol, hw already stripped it */
      }

      memcpy (&msg.content, &po_hi_c_driver_spacewire_rxpkt[j], __PO_HI_MESSAGES_MAX_SIZE + j);

      __po_hi_unmarshall_request (&request, &msg);

      printf ("[RASTA SPACEWIRE] Destination port: %d\n", request.port);
      __po_hi_main_deliver (&request);
   }
}

void __po_hi_c_driver_spacewire_rasta_init (char* name, char* location)
{
   unsigned int node_addr;

   node_addr = atoi (location);

   __DEBUGMSG ("[RASTA SPACEWIRE] Init\n");

   init_pci();

   __DEBUGMSG ("[RASTA SPACEWIRE] Initializing RASTA ...");

   if  (rasta_register ())
   {
      __DEBUGMSG(" ERROR !\n");
     return;
   }
   __DEBUGMSG(" OK !\n");

   __DEBUGMSG ("[RASTA SPACEWIRE] Open spacewire device ...");

   po_hi_c_driver_rasta_spacewire_fd = open (__PO_HI_DRIVER_SPACEWIRE_RASTA_DEVICE, O_RDWR);

   if (po_hi_c_driver_rasta_spacewire_fd < 0)
   {
      __DEBUGMSG(" ERROR !\n");
      return;
   }

   __DEBUGMSG(" OK !\n");

   __DEBUGMSG ("[RASTA SPACEWIRE] Configure spacewire device node address = %d ...", node_addr);

   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd,SPACEWIRE_IOCTRL_SET_COREFREQ,30000); 
   /* make driver calculate timings from 30MHz spacewire clock */
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd,SPACEWIRE_IOCTRL_SET_NODEADDR, node_addr);
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd,SPACEWIRE_IOCTRL_SET_RXBLOCK,1);
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd,SPACEWIRE_IOCTRL_SET_TXBLOCK,0);
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd,SPACEWIRE_IOCTRL_SET_TXBLOCK_ON_FULL,1);
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd,SPACEWIRE_IOCTRL_SET_RM_PROT_ID,1);
   /* remove protocol id */
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd,SPACEWIRE_IOCTRL_START,2000);
}

int __po_hi_c_driver_spacewire_rasta_sender (const __po_hi_task_id task_id, const __po_hi_port_t port)
{
   int len = -1;
   int i;
   __po_hi_local_port_t local_port;
   __po_hi_request_t* request;
   __po_hi_msg_t msg;
   __po_hi_port_t destination_port;

   local_port = __po_hi_get_local_port_from_global_port (port);

   request = __po_hi_gqueue_get_most_recent_value (task_id, local_port);

   destination_port     = __po_hi_gqueue_get_destination (task_id, local_port, 0);

   __po_hi_msg_reallocate (&msg);

   request->port = destination_port;

   __po_hi_marshall_request (request, &msg);

   __DEBUGMSG ("[RASTA SPACEWIRE] Send packet destination port = %d ...", destination_port);

   for(i=0; i<1; i++)
   {
      po_hi_c_driver_rasta_spacewire_init_pkt(&po_hi_c_driver_spacewire_txpkts[i]);
   }

   memcpy (po_hi_c_driver_spacewire_txpkts[0].data, &msg, __PO_HI_MESSAGES_MAX_SIZE);

   len = write (po_hi_c_driver_rasta_spacewire_fd, po_hi_c_driver_spacewire_txpkts, __PO_HI_DRIVER_RASTA_SPACEWIRE_PKTSIZE + 4);

   if (len < 0)
   {
      __DEBUGMSG (" failed !\n");
   }
   else
   {
      __DEBUGMSG (" OK !\n");
   }
   return 1;
}

#endif /* __PO_HI_NEED_DRIVER_SPACEWIRE_RASTA */


