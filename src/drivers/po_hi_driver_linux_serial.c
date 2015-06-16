/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2010-2014 ESA & ISAE.
 */

#include <drivers/po_hi_driver_linux_serial.h>
#include <drivers/configuration/serial.h>

#if defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX_SENDER) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX_RECEIVER)

#include <po_hi_debug.h>
#include <po_hi_returns.h>
#include <po_hi_utils.h>
#include <po_hi_messages.h>
#include <po_hi_transport.h>
#include <po_hi_gqueue.h>
#include <drivers/po_hi_driver_serial_common.h>
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
/* Linux-specific files */

int      po_hi_c_driver_serial_fd_read;
int      po_hi_c_driver_serial_fd_write;
uint32_t po_hi_c_driver_serial_sending_wait;

#if defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX_RECEIVER)

__po_hi_request_t __po_hi_c_driver_serial_linux_request;
__po_hi_msg_t     __po_hi_c_driver_serial_linux_poller_msg;
void __po_hi_c_driver_serial_linux_poller (const __po_hi_device_id dev_id)
{
   (void) dev_id;
   int n;
   int ts;

   unsigned long* swap_pointer;
   unsigned long swap_value;


   __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Hello, i'm the serial poller , must read %d bytes!\n", __PO_HI_MESSAGES_MAX_SIZE);

   __po_hi_msg_reallocate (&__po_hi_c_driver_serial_linux_poller_msg);
   n = 0;
   while (n < __PO_HI_MESSAGES_MAX_SIZE)
   {
       if (read (po_hi_c_driver_serial_fd_read, &(__po_hi_c_driver_serial_linux_poller_msg.content[n]), 1) != 1)
	{
	    __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Cannot read on socket !\n");
	    return;
	}

	n++;
   }


   if (n == 0)
   {
    __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] n=0 !\n");
      return;
   }

   if (n != __PO_HI_MESSAGES_MAX_SIZE)
   {
      __PO_HI_DEBUG_CRITICAL ("[LINUX SERIAL] Inconsistent received message size (received %d bytes)!\n", n);
      return;
   }

   __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] read() returns %d\n", n);

   swap_pointer  = (unsigned long*) &__po_hi_c_driver_serial_linux_poller_msg.content[0];
   swap_value    = *swap_pointer;
   *swap_pointer = __po_hi_swap_byte (swap_value);

   __po_hi_c_driver_serial_linux_poller_msg.length = n;

   __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Message after swapped port: 0x");
   for (ts = 0 ; ts < __po_hi_c_driver_serial_linux_poller_msg.length ; ts++)
   {
        __PO_HI_DEBUG_DEBUG ("%x", __po_hi_c_driver_serial_linux_poller_msg.content[ts]);
   }
   __PO_HI_DEBUG_DEBUG ("\n");

   __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Received: %s\n", __po_hi_c_driver_serial_linux_poller_msg.content);

   __po_hi_unmarshall_request (&__po_hi_c_driver_serial_linux_request, &__po_hi_c_driver_serial_linux_poller_msg);

   if (__po_hi_c_driver_serial_linux_request.port > __PO_HI_NB_PORTS)
   {
      __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Invalid port number !\n");
      return;
   }

   __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Destination port: %d\n", __po_hi_c_driver_serial_linux_request.port);
   __po_hi_main_deliver (&__po_hi_c_driver_serial_linux_request);
}
#endif


#if defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX_SENDER)

void __po_hi_c_driver_serial_linux_init_sender (__po_hi_device_id id)
{
   struct termios             oldtio,newtio;
   __po_hi_c_serial_conf_t*   serialconf;

   po_hi_c_driver_serial_sending_wait = 0;

   __PO_HI_DEBUG_INFO ("[LINUX SERIAL] Init sender\n");

   __po_hi_transport_set_sending_func (id, __po_hi_c_driver_serial_linux_sender);

   serialconf = (__po_hi_c_serial_conf_t*)__po_hi_get_device_configuration (id);

   if (serialconf == NULL)
   {
      __PO_HI_DEBUG_INFO ("[LINUX SERIAL] Cannot get the configuration of the device !\n");
      return;
   }

   if (serialconf->exist.sending_wait == 1)
   {
      po_hi_c_driver_serial_sending_wait = (uint32_t) serialconf->sending_wait;
      __PO_HI_DEBUG_INFO ("[LINUX SERIAL] Set sending delay to %u!\n",po_hi_c_driver_serial_sending_wait);
   }

   po_hi_c_driver_serial_fd_write = open (serialconf->devname, O_WRONLY | O_NOCTTY | O_NDELAY);

   if (po_hi_c_driver_serial_fd_write < 0)
   {
      __PO_HI_DEBUG_CRITICAL ("[LINUX SERIAL] Error while opening device %s\n", serialconf->devname);
   }
   else
   {
      __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Device %s successfully opened for sending, fd=%d\n", serialconf->devname, po_hi_c_driver_serial_fd_write);
   }

   tcgetattr (po_hi_c_driver_serial_fd_write, &oldtio);  /* save current serial port settings */
   tcgetattr (po_hi_c_driver_serial_fd_write, &newtio);  /* save current serial port settings */
        
   newtio.c_cflag |= CREAD ;
   newtio.c_iflag = IGNPAR | IGNBRK;
   newtio.c_lflag |= ICANON;
   newtio.c_cc[VMIN]=1;
   newtio.c_cc[VTIME]=0;
   cfmakeraw (&newtio);

   switch (__po_hi_c_driver_serial_common_get_speed (id))
   {
      case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_19200:
         newtio.c_cflag |= B19200;
         __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Set speed to 19200\n");
         break;

      case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_38400:
         newtio.c_cflag |= B38400;
         __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Set speed to 38400\n");
         break;

      case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_57600:
         newtio.c_cflag |= B57600;
         __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Set speed to 57600\n");
         break;

      case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_115200:
         __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Set speed to 115200\n");
         newtio.c_cflag |= B115200;
         break;

      case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_UNKNWON:
         __PO_HI_DEBUG_INFO ("[LINUX SERIAL] Unknwon speed for the serial line\n");
         break;
   }

   /* 
    * clean the serial line and activate the settings for the port
    */
   if (tcflush (po_hi_c_driver_serial_fd_write, TCIOFLUSH) == -1)
   {
      __PO_HI_DEBUG_CRITICAL ("[LINUX SERIAL] Error in tcflush()\n");
   }

   if (tcsetattr (po_hi_c_driver_serial_fd_write, TCSANOW, &newtio) == -1)
   {
      __PO_HI_DEBUG_CRITICAL ("[LINUX SERIAL] Error in tcsetattr()\n");
   }

    __PO_HI_DEBUG_INFO ("[LINUX SERIAL] End of init\n");
}
#endif


#if defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX_RECEIVER)
void __po_hi_c_driver_serial_linux_init_receiver (__po_hi_device_id id)
{
   struct termios             oldtio,newtio;
   __po_hi_c_serial_conf_t*   serialconf;

   __PO_HI_DEBUG_INFO ("[LINUX SERIAL] Init receiver\n");

   serialconf = (__po_hi_c_serial_conf_t*)__po_hi_get_device_configuration (id);

   if (serialconf == NULL)
   {
      __PO_HI_DEBUG_INFO ("[LINUX SERIAL] Cannot get the name of the device !\n");
      return;
   }

   po_hi_c_driver_serial_fd_read = open (serialconf->devname, O_RDONLY | O_NOCTTY);

   if (po_hi_c_driver_serial_fd_read < 0)
   {
      __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Error while opening device %s\n", serialconf->devname);
   }
   else
   {
      __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Device %s successfully opened for reading, fd=%d\n", serialconf->devname , po_hi_c_driver_serial_fd_read);
   }


   tcgetattr (po_hi_c_driver_serial_fd_read, &oldtio);  /* save current serial port settings */
   tcgetattr (po_hi_c_driver_serial_fd_read, &newtio);  /* save current serial port settings */
        
   newtio.c_cflag |= CREAD ;
   newtio.c_iflag = IGNPAR | IGNBRK;
   newtio.c_lflag |= ICANON;
   newtio.c_cc[VMIN]=1;
   newtio.c_cc[VTIME]=0;
   cfmakeraw (&newtio);

   switch (__po_hi_c_driver_serial_common_get_speed (id))
   {
      case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_19200:
         newtio.c_cflag |= B19200;
         __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Set speed to 19200\n");
         break;

      case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_38400:
         newtio.c_cflag |= B38400;
         __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Set speed to 38400\n");
         break;

      case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_57600:
         newtio.c_cflag |= B57600;
         __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Set speed to 57600\n");
         break;

      case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_115200:
         __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Set speed to 115200\n");
         newtio.c_cflag |= B115200;
         break;

      case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_UNKNWON:
         __PO_HI_DEBUG_INFO ("[LINUX SERIAL] Unknwon speed for the serial line\n");
         break;
   }

   if (tcflush (po_hi_c_driver_serial_fd_read, TCIOFLUSH) == -1)
   {
      __PO_HI_DEBUG_CRITICAL ("[LINUX SERIAL] Error in tcflush()\n");
   }

   if (tcsetattr (po_hi_c_driver_serial_fd_read, TCSANOW, &newtio) == -1)
   {
      __PO_HI_DEBUG_CRITICAL ("[LINUX SERIAL] Error in tcsetattr()\n");
   }

    __PO_HI_DEBUG_INFO ("[LINUX SERIAL] End of init\n");
}
#endif


#if defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX)

void __po_hi_c_driver_serial_linux_init (__po_hi_device_id id)
{

   __po_hi_c_driver_serial_linux_init_receiver (id);
   __po_hi_c_driver_serial_linux_init_sender (id);
   return;
}
#endif


#if defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX_SENDER)

__po_hi_msg_t __po_hi_c_driver_serial_linux_sender_msg;

int  __po_hi_c_driver_serial_linux_sender (__po_hi_task_id task_id, __po_hi_port_t port)
{
   int                     n;
   int                     ts;
   unsigned long*          swap_pointer;
   unsigned long           swap_value;
   __po_hi_local_port_t    local_port;
   __po_hi_request_t*      request;
   __po_hi_port_t          destination_port;

   local_port = __po_hi_get_local_port_from_global_port (port);

   request = __po_hi_gqueue_get_most_recent_value (task_id, local_port);

   if (request->port == -1)
   {
      __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Send output task %d, port %d (local_port=%d): no value to send\n", task_id, port, local_port);
      return __PO_HI_SUCCESS;
   }

   destination_port     = __po_hi_gqueue_get_destination (task_id, local_port, 0);

   __po_hi_msg_reallocate (&__po_hi_c_driver_serial_linux_sender_msg);

   request->port = destination_port;

   __po_hi_marshall_request (request, &__po_hi_c_driver_serial_linux_sender_msg);

   /* Swap only the port (first 32 bytes) */
   swap_pointer  = (unsigned long*) &__po_hi_c_driver_serial_linux_sender_msg.content[0];
   swap_value    = *swap_pointer;
   *swap_pointer = __po_hi_swap_byte (swap_value);

   if (po_hi_c_driver_serial_sending_wait != 0)
   {
      for (n = 0 ; n < __PO_HI_MESSAGES_MAX_SIZE ; n++)
      {
         write (po_hi_c_driver_serial_fd_write, &(__po_hi_c_driver_serial_linux_sender_msg.content[n]), 1);
         usleep (po_hi_c_driver_serial_sending_wait);
      }

   }
   else
   {
      n = write (po_hi_c_driver_serial_fd_write, &__po_hi_c_driver_serial_linux_sender_msg, __PO_HI_MESSAGES_MAX_SIZE);
   }

   __PO_HI_DEBUG_DEBUG  ("[LINUX SERIAL] write() returns %d, message sent: 0x", n);

   for (ts = 0 ; ts < __PO_HI_MESSAGES_MAX_SIZE ; ts++)
   {
      __PO_HI_DEBUG_DEBUG ("%x", __po_hi_c_driver_serial_linux_sender_msg.content[ts]);
   }
   __PO_HI_DEBUG_DEBUG ("\n");

   request->port = __PO_HI_GQUEUE_INVALID_PORT;

   return 1;
}
#endif

#endif
