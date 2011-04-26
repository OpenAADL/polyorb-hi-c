/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * Copyright (C) 2010, European Space Agency
 */

#include <deployment.h>
/* Generated code header */

#ifdef __PO_HI_NEED_DRIVER_SERIAL_RASTA

#include <activity.h>
#include <marshallers.h>

#include <po_hi_debug.h>
#include <po_hi_transport.h>
#include <po_hi_gqueue.h>
#include <po_hi_messages.h>
#include <po_hi_returns.h>
#include <po_hi_utils.h>
#include <drivers/po_hi_rtems_utils.h>
#include <drivers/po_hi_driver_rasta_serial.h>
#include <drivers/po_hi_driver_rasta_common.h>

#include <drivers/po_hi_driver_serial_common.h>

#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>
#include <termios.h>
/* POSIX-style files */

#include <pci.h>
#include <rasta.h>
#include <apbuart_rasta.h>
/* Rasta includes from GAISLER drivers */

#include <drivers/configuration/serial.h>

int po_hi_c_driver_rasta_serial_fd;

__po_hi_msg_t        __po_hi_c_driver_rasta_serial_msg;
__po_hi_request_t    __po_hi_c_driver_rasta_serial_request;

void __po_hi_c_driver_serial_rasta_poller (void)
{

   int n;
   int ts;
   int tr;
   uint8_t* ptr;

   __PO_HI_DEBUG_INFO ("[RASTA SERIAL] Poller waits for incoming message !\n");
   ts = __PO_HI_MESSAGES_MAX_SIZE;
   tr = 0;
   ptr = &(__po_hi_c_driver_rasta_serial_msg.content[0]);
   __po_hi_msg_reallocate (&__po_hi_c_driver_rasta_serial_msg);
   while (ts > 0)
   {
      n = read (po_hi_c_driver_rasta_serial_fd, ptr, ts); 
      ptr += n;

      if (n == -1)
      {
         __PO_HI_DEBUG_DEBUG ("[RASTA SERIAL] Cannot read on socket !\n");
         return;
      }
      ts -= n;
   tr += n;
   }

#ifdef __PO_HI_DEBUG_INFO
   __PO_HI_DEBUG_INFO ("[RASTA SERIAL] read() returns total %d, max message size=%d\n", tr, __PO_HI_MESSAGES_MAX_SIZE);

   __PO_HI_DEBUG_INFO ("[RASTA SERIAL] Message received by poller: 0x");
   for (ts = 0 ; ts < __PO_HI_MESSAGES_MAX_SIZE ; ts++)
   {
      __PO_HI_DEBUG_INFO ("%x", __po_hi_c_driver_rasta_serial_msg.content[ts]);
   }
   __PO_HI_DEBUG_INFO ("\n");
#endif

   __po_hi_c_driver_rasta_serial_msg.length = tr;

   __po_hi_unmarshall_request (&__po_hi_c_driver_rasta_serial_request,
                               &__po_hi_c_driver_rasta_serial_msg);

   __po_hi_main_deliver (&__po_hi_c_driver_rasta_serial_request);
}

extern amba_confarea_type* __po_hi_driver_rasta_common_get_bus ();
void __po_hi_rasta_interrrupt_register(void *handler, int irqno, void *arg);

void __po_hi_c_driver_serial_rasta_init (__po_hi_device_id id)
{
   __po_hi_c_serial_conf_t* serialconf;

   __po_hi_c_driver_rasta_common_init ();

   serialconf = (__po_hi_c_serial_conf_t*)__po_hi_get_device_configuration (id);

   if (serialconf == NULL)
   {
      __PO_HI_DEBUG_INFO ("[RASTA SERIAL] Cannot get the name of the device !\n");
      return;
   }

    /* provide the spacewire driver with AMBA Plug&Play
     * info so that it can find the GRSPW cores.
     */

   __PO_HI_DEBUG_INFO ("[RASTA SERIAL] Initialization starts !\n");

   po_hi_c_driver_rasta_serial_fd = open (serialconf->devname, O_RDWR);

   if (po_hi_c_driver_rasta_serial_fd < 0)
   {
      __PO_HI_DEBUG_CRITICAL ("[RASTA SERIAL] Error while opening device %s\n", serialconf->devname);
   }
   __PO_HI_DEBUG_DEBUG ("[RASTA SERIAL] Device open, fd=%d\n", po_hi_c_driver_rasta_serial_fd);

   switch (__po_hi_c_driver_serial_common_get_speed (id))
   {
      case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_19200:
         __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd, APBUART_SET_BAUDRATE, 19200);
         break;

      case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_38400:
         __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd, APBUART_SET_BAUDRATE, 38400);
         break;

      case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_57600:
         __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd, APBUART_SET_BAUDRATE, 57600);
         break;

      case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_115200:
         __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd, APBUART_SET_BAUDRATE, 115200);
         break;

      case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_UNKNWON:
         __PO_HI_DEBUG_INFO ("[RASTA SERIAL] Unknwon speed for the serial line\n");
         break;
   }

  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd, APBUART_SET_BLOCKING, APBUART_BLK_RX | APBUART_BLK_TX | APBUART_BLK_FLUSH);
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd, APBUART_SET_TXFIFO_LEN, 64);  /* Transmitt buffer 64 chars */
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd, APBUART_SET_RXFIFO_LEN, 256); /* Receive buffer 256 chars */
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd, APBUART_SET_ASCII_MODE, 0); /* Make \n go \n\r or \r\n */
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd, APBUART_CLR_STATS, 0);
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd, APBUART_START, 0);

  if (tcflush (po_hi_c_driver_rasta_serial_fd, TCIOFLUSH) != 0)
  {
     __PO_HI_DEBUG_CRITICAL ("[RASTA SERIAL] Error when trying to flush\n");
  }
  __PO_HI_DEBUG_INFO ("[RASTA SERIAL] Initialization complete !\n");
}

int __po_hi_c_driver_serial_rasta_sender (const __po_hi_task_id task_id, const __po_hi_port_t port)
{
   int n;
   int ts;
   __po_hi_local_port_t local_port;
   __po_hi_request_t* request;
   __po_hi_msg_t msg;
   __po_hi_port_t destination_port;

   local_port = __po_hi_get_local_port_from_global_port (port);

   request = __po_hi_gqueue_get_most_recent_value (task_id, local_port);

   if (request->port == -1)
   {
      __PO_HI_DEBUG_DEBUG ("[RASTA SERIAL] Send output task %d, port %d (local_port=%d): no value to send\n", task_id, port, local_port);
      return __PO_HI_SUCCESS;
   }

   destination_port     = __po_hi_gqueue_get_destination (task_id, local_port, 0);

   __po_hi_msg_reallocate (&msg);

   request->port = destination_port;
   __PO_HI_DEBUG_INFO ("[RASTA SERIAL] Destination port= %d\n", destination_port);

   __po_hi_marshall_request (request, &msg);

   __PO_HI_DEBUG_INFO ("[RASTA SERIAL] Message sent: 0x");
#ifdef __PO_HI_DEBUG_LEVEL_INFO
   for (ts = 0 ; ts < __PO_HI_MESSAGES_MAX_SIZE ; ts++)
   {
      __PO_HI_DEBUG_INFO ("%x", msg.content[ts]);
   }
#endif

   __PO_HI_DEBUG_INFO ("\n");

   n = write (po_hi_c_driver_rasta_serial_fd, &msg, __PO_HI_MESSAGES_MAX_SIZE);

   __PO_HI_DEBUG_DEBUG ("[RASTA SERIAL] write() returns %d\n", n);

   request->port = __PO_HI_GQUEUE_INVALID_PORT;

   return 1;
}

#endif

