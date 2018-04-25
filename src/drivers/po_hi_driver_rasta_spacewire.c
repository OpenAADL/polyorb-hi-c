/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2010-2018 ESA & ISAE.
 */

#include <deployment.h>
/* Generated code header */

#ifdef __PO_HI_NEED_DRIVER_SPACEWIRE_RASTA

#include <string.h> // for memcpy
#include <activity.h>
#include <marshallers.h>
#include <deployment.h>

#include <po_hi_debug.h>
#include <po_hi_transport.h>
#include <po_hi_gqueue.h>
#include <po_hi_messages.h>
#include <po_hi_returns.h>


#include <drivers/po_hi_rtems_utils.h>
#include <drivers/po_hi_driver_rasta_spacewire.h>
#include <drivers/po_hi_driver_rasta_common.h>

#include <stdlib.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
/* POSIX-style files */


#include <rtems/bspIo.h>
#include <ambapp.h>

#ifdef GRLEON2
#include <pci.h>
#include <rasta.h>
#include <grspw_rasta.h>
#include <apbuart_rasta.h>
#endif

#if defined GRLEON3 && defined RTEMS412
#include <rtems.h>
#include <bsp/grspw.h>
#endif


/* Rasta includes from GAISLER drivers */

__po_hi_request_t    __po_hi_c_driver_spacewire_rasta_request;
__po_hi_msg_t        __po_hi_c_driver_spacewire_rasta_poller_msg;
int                  po_hi_c_driver_rasta_spacewire_fd[__PO_HI_NB_DEVICES];
char                 __po_hi_c_driver_rasta_spacewire_sndbuf[__PO_HI_MESSAGES_MAX_SIZE + 1];

void __po_hi_c_driver_spacewire_rasta_poller (const __po_hi_device_id dev_id)
{
   int len;
   int ts;

   __PO_HI_DEBUG_DEBUG ("[RASTA SPACEWIRE] Hello, i'm the spacewire poller !\n");

   __po_hi_msg_reallocate (&__po_hi_c_driver_spacewire_rasta_poller_msg);

   len = read (po_hi_c_driver_rasta_spacewire_fd[dev_id],
               &__po_hi_c_driver_spacewire_rasta_poller_msg.content[0],
               __PO_HI_MESSAGES_MAX_SIZE);

   __PO_HI_DEBUG_DEBUG ("[RASTA SPACEWIRE] Poller received a message, len=%d\n", len);
   if (len < 0)
   {
      __PO_HI_DEBUG_CRITICAL ("[RASTA SPACEWIRE] Error while reading\n");
   }
   else
   {

      __PO_HI_DEBUG_DEBUG ("Message content: |0x");
      for (ts = 0 ; ts < __PO_HI_MESSAGES_MAX_SIZE ; ts++)
      {
         __PO_HI_DEBUG_DEBUG ("%x", __po_hi_c_driver_spacewire_rasta_poller_msg.content[ts]);
      }
      __PO_HI_DEBUG_DEBUG ("|\n");

      __po_hi_c_driver_spacewire_rasta_poller_msg.length = __PO_HI_MESSAGES_MAX_SIZE;
      __po_hi_unmarshall_request (&__po_hi_c_driver_spacewire_rasta_request, &__po_hi_c_driver_spacewire_rasta_poller_msg);

      __PO_HI_DEBUG_DEBUG ("[RASTA SPACEWIRE] Destination port: %d\n",__po_hi_c_driver_spacewire_rasta_request.port);
      __po_hi_main_deliver (&__po_hi_c_driver_spacewire_rasta_request);
   }
}


extern rtems_isr __po_hi_rasta_interrupt_handler (rtems_vector_number v);
extern unsigned int __po_hi_driver_rasta_bar0, __po_hi_driver_rasta_bar1;

void __po_hi_rasta_interrrupt_register(void *handler, int irqno, void *arg);

#if defined RTEMS48 || defined RTEMS410
extern amba_confarea_type* __po_hi_driver_rasta_common_get_bus ();
#elif RTEMS411
extern struct ambapp_bus * __po_hi_driver_rasta_common_get_bus ();
#elif RTEMS412
 ;
#else
#error "o<"
#endif

void __po_hi_c_driver_spacewire_rasta_init (__po_hi_device_id id)
{
   unsigned int node_addr;
   __po_hi_c_spacewire_conf_t* drv_conf;

   drv_conf = (__po_hi_c_spacewire_conf_t*) __po_hi_get_device_configuration (id);

   node_addr = drv_conf->nodeaddr;

   __PO_HI_DEBUG_INFO ("[RASTA SPACEWIRE] Init, node address=%d\n", node_addr);

   __po_hi_c_driver_rasta_common_init ();

   __po_hi_transport_set_sending_func (id, __po_hi_c_driver_spacewire_rasta_sender);

   __PO_HI_DEBUG_DEBUG ("[RASTA SPACEWIRE] Open spacewire device %s ...", drv_conf->devname);

   po_hi_c_driver_rasta_spacewire_fd[id] = open (drv_conf->devname, O_RDWR);

   if (po_hi_c_driver_rasta_spacewire_fd[id] < 0)
   {
      __PO_HI_DEBUG_DEBUG (" ERROR !\n");
      return;
   }

   __PO_HI_DEBUG_DEBUG (" OK !\n");

   __PO_HI_DEBUG_DEBUG ("[RASTA SPACEWIRE] Configure spacewire device node address = %d ...", node_addr);

/*
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd, SPACEWIRE_IOCTRL_SET_COREFREQ, 0);                 // Core frequency in KHz (0 = full speed)
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd, SPACEWIRE_IOCTRL_SET_CLKDIV, 2);                   // Clock division factor
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd, SPACEWIRE_IOCTRL_SET_RMAPEN, 1);                   // No RMAP
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd, SPACEWIRE_IOCTRL_SET_NODEADDR, node_addr);         // Not necessary
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd, SPACEWIRE_IOCTRL_SET_RXBLOCK, 1);                  // Blocking read
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd, SPACEWIRE_IOCTRL_SET_CHECK_RMAP, 0);               // Do not check RMAP CRC
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd, SPACEWIRE_IOCTRL_SET_RM_PROT_ID, 0);               // Do not remove protocol id
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd, SPACEWIRE_IOCTRL_SET_TXBLOCK, 0);                  // Non blocking write
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd, SPACEWIRE_IOCTRL_SET_TXBLOCK_ON_FULL, 1);          // Blocking write if full
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd, SPACEWIRE_IOCTRL_SET_PROMISCUOUS, 1);              // Receive from any source
*/

   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd[id],SPACEWIRE_IOCTRL_STOP,NULL);
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd[id],SPACEWIRE_IOCTRL_SET_DISCONNECT,43);
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd[id],SPACEWIRE_IOCTRL_SET_COREFREQ,30000);
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd[id],SPACEWIRE_IOCTRL_SET_RXBLOCK,1);
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd[id],SPACEWIRE_IOCTRL_SET_TXBLOCK,1);
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd[id],SPACEWIRE_IOCTRL_SET_NODEADDR, (unsigned char)node_addr); //
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd[id],SPACEWIRE_IOCTRL_SET_PROMISCUOUS,1); // 
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd[id],SPACEWIRE_IOCTRL_SET_CLKDIV, 0);
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd[id],SPACEWIRE_IOCTRL_SET_TXBLOCK_ON_FULL,1);
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd[id],SPACEWIRE_IOCTRL_SET_RM_PROT_ID,0);
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd[id],SPACEWIRE_IOCTRL_START,2000);

#ifdef RTEMS412
   spw_config *cnf = (spw_config *)malloc(sizeof(spw_config));
   __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_spacewire_fd[id],SPACEWIRE_IOCTRL_GET_CONFIG,cnf);
   __PO_HI_DEBUG_DEBUG("******** SPW_CONFIG ********  \n");
   __PO_HI_DEBUG_DEBUG("Node Address: %i\n", cnf->nodeaddr);
   __PO_HI_DEBUG_DEBUG("Destination Key: %i\n", cnf->destkey);
   __PO_HI_DEBUG_DEBUG("Clock Divider: %i\n", cnf->clkdiv);
   __PO_HI_DEBUG_DEBUG("Rx Maximum Packet: %i\n", cnf->rxmaxlen);
   __PO_HI_DEBUG_DEBUG("Timer: %i\n", cnf->timer);
   __PO_HI_DEBUG_DEBUG("Disconnect: %i\n", cnf->disconnect);
   __PO_HI_DEBUG_DEBUG("Promiscuous: %i\n", cnf->promiscuous);
   __PO_HI_DEBUG_DEBUG("RMAP Enable: %i\n", cnf->rmapen);
   __PO_HI_DEBUG_DEBUG("RMAP Buffer Disable: %i\n", cnf->rmapbufdis);
   __PO_HI_DEBUG_DEBUG("Linkdisabled: %i\n", cnf->linkdisabled);
   __PO_HI_DEBUG_DEBUG("Linkstart: %i\n", cnf->linkstart);
   __PO_HI_DEBUG_DEBUG("Check Rmap Error: %i\n", cnf->check_rmap_err);
   __PO_HI_DEBUG_DEBUG("Remove Protocol ID: %i\n", cnf->rm_prot_id);
   __PO_HI_DEBUG_DEBUG("Blocking Transmit: %i\n", cnf->tx_blocking);
   __PO_HI_DEBUG_DEBUG("Blocking Tx when buffer full: %i\n", cnf->tx_block_on_full);
   __PO_HI_DEBUG_DEBUG("Blocking Receive: %i\n", cnf->rx_blocking);
   __PO_HI_DEBUG_DEBUG("Disable when Link Error: %i\n", cnf->disable_err);
   __PO_HI_DEBUG_DEBUG("Link Error IRQ Enabled: %i\n", cnf->link_err_irq);
   __PO_HI_DEBUG_DEBUG("Link Error Event Task ID: %i\n", cnf->event_id);
   __PO_HI_DEBUG_DEBUG("RMAP Available: %i\n", cnf->is_rmap);
   __PO_HI_DEBUG_DEBUG("RMAP CRC Available: %i\n", cnf->is_rmapcrc);
   __PO_HI_DEBUG_DEBUG("Unaligned Receive Buffer Support: %i\n", cnf->is_rxunaligned);
   __PO_HI_DEBUG_DEBUG("Read Nodemask: %i\n", cnf->nodemask);
   __PO_HI_DEBUG_DEBUG("Read Timeout: %i\n", cnf->rtimeout);
   __PO_HI_DEBUG_DEBUG("Keep source address in userbuffer: %i\n", cnf->keep_source);
   __PO_HI_DEBUG_DEBUG("\n");
#endif
}

__po_hi_msg_t           __po_hi_c_driver_spacewire_rasta_sender_msg;

int __po_hi_c_driver_spacewire_rasta_sender (const __po_hi_task_id task_id, const __po_hi_port_t port)
{
   int len = -1;
   int i;

   __po_hi_c_spacewire_conf_t* sender_conf;
   __po_hi_c_spacewire_conf_t* receiver_conf;

   __po_hi_local_port_t    local_port;
   __po_hi_request_t*      request;
   __po_hi_port_t          destination_port;

   __po_hi_device_id       dev_id;

   dev_id = __po_hi_get_device_from_port (port);

   if (dev_id == invalid_device_id)
   {
      __PO_HI_DEBUG_DEBUG ("[RASTA SPW] Invalid device id for sending\n");
      return __PO_HI_UNAVAILABLE;
   }

   local_port = __po_hi_get_local_port_from_global_port (port);

   request = __po_hi_gqueue_get_most_recent_value (task_id, local_port);

   if (request->port == -1)
   {
      __PO_HI_DEBUG_DEBUG ("[RASTA SPACEWIRE] Send output task %d, port %d : no value to send\n", task_id, port);
      return __PO_HI_SUCCESS;
   }

   destination_port     = __po_hi_gqueue_get_destination (task_id, local_port, 0);

   __po_hi_msg_reallocate (&__po_hi_c_driver_spacewire_rasta_sender_msg);

   request->port = destination_port;

   sender_conf = (__po_hi_c_spacewire_conf_t*) __po_hi_get_device_configuration (dev_id);
   receiver_conf = (__po_hi_c_spacewire_conf_t*) __po_hi_get_device_configuration (__po_hi_get_device_from_port (destination_port));

   __po_hi_marshall_request (request, &__po_hi_c_driver_spacewire_rasta_sender_msg);

   len = -1;
   if (sender_conf->use_router == TRUE)
   {
      __po_hi_c_driver_rasta_spacewire_sndbuf[0] = receiver_conf->nodeaddr;
      memcpy (&__po_hi_c_driver_rasta_spacewire_sndbuf[1], __po_hi_c_driver_spacewire_rasta_sender_msg.content , __PO_HI_MESSAGES_MAX_SIZE);
      len = write (po_hi_c_driver_rasta_spacewire_fd[dev_id], __po_hi_c_driver_rasta_spacewire_sndbuf, __PO_HI_MESSAGES_MAX_SIZE + 1);
   }
   else
   {
      len = write (po_hi_c_driver_rasta_spacewire_fd[dev_id], __po_hi_c_driver_spacewire_rasta_sender_msg.content, __PO_HI_MESSAGES_MAX_SIZE);
   }

   fsync(po_hi_c_driver_rasta_spacewire_fd[dev_id]);

   if (len < 0)
   {
      __PO_HI_DEBUG_CRITICAL (" [RASTA SPACEWIRE] failed !\n");
   }
   else if((0 <= len)&(len < __PO_HI_MESSAGES_MAX_SIZE))
   {
      __PO_HI_DEBUG_CRITICAL (" [RASTA SPACEWIRE] Unable write !\n");
   }
   else
   {
      __PO_HI_DEBUG_DEBUG (" [RASTA SPACEWIRE] OK !\n");
   }

   request->port = __PO_HI_GQUEUE_INVALID_PORT;

   return 1;
}

#endif /* __PO_HI_NEED_DRIVER_SPACEWIRE_RASTA */
