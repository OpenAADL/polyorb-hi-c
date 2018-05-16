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

#if defined (__PO_HI_NEED_DRIVER_SERIAL_LEON) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LEON_SENDER) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LEON_RECEIVER)

#include <po_hi_debug.h>
#include <po_hi_utils.h>
#include <po_hi_messages.h>
#include <po_hi_transport.h>
#include <po_hi_gqueue.h>
#include <drivers/po_hi_driver_serial_common.h>
#include <drivers/po_hi_driver_leon_serial.h>
#include <drivers/configuration/serial.h>
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

int po_hi_c_driver_leon_serial_fd_read;
int po_hi_c_driver_leon_serial_fd_write;

#if defined (__PO_HI_NEED_DRIVER_SERIAL_LEON) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LEON_RECEIVER)


 __po_hi_request_t  po_hi_c_driver_leon_serial_request;
 __po_hi_msg_t      po_hi_c_driver_leon_serial_poller_msg;

void __po_hi_c_driver_serial_leon_poller (const __po_hi_device_id dev_id)
{
   int n;
   int ts;
   int tr;

   (void) dev_id;


   __PO_HI_DEBUG_DEBUG ("[LEON SERIAL] Hello, i'm the serial poller , must read %d bytes on %d !\n", __PO_HI_MESSAGES_MAX_SIZE, po_hi_c_driver_leon_serial_fd_read);

   __po_hi_msg_reallocate (&po_hi_c_driver_leon_serial_poller_msg);

   tr = 0;
   while (tr < __PO_HI_MESSAGES_MAX_SIZE)
   {
      if (read (po_hi_c_driver_leon_serial_fd_read, &(po_hi_c_driver_leon_serial_poller_msg.content[tr]), 1) == 1)
      {
         tr++;
      }
   }

   po_hi_c_driver_leon_serial_poller_msg.length = __PO_HI_MESSAGES_MAX_SIZE;
  __PO_HI_DEBUG_DEBUG ("[LEON SERIAL] read() syscall returns in total %d, received: ", tr);
#ifdef __PO_HI_DEBUG_DEBUG
   __PO_HI_DEBUG_DEBUG("[LEON SERIAL] Message received: 0x");
   for (ts = 0 ; ts < po_hi_c_driver_leon_serial_poller_msg.length ; ts++)
   {
        __PO_HI_DEBUG_DEBUG ("%x", po_hi_c_driver_leon_serial_poller_msg.content[ts]);
   }
   __PO_HI_DEBUG_DEBUG ("\n");
#endif

   __po_hi_unmarshall_request (& po_hi_c_driver_leon_serial_request, &po_hi_c_driver_leon_serial_poller_msg);

   if ( po_hi_c_driver_leon_serial_request.port > __PO_HI_NB_PORTS)
   {
      __PO_HI_DEBUG_WARNING ("[LEON SERIAL] Invalid port number !\n");
      return;
   }

   __PO_HI_DEBUG_INFO ("[LEON SERIAL] Destination port: %d\n",  po_hi_c_driver_leon_serial_request.port);
   __po_hi_main_deliver (& po_hi_c_driver_leon_serial_request);
}
#endif


#if defined (__PO_HI_NEED_DRIVER_SERIAL_LEON) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LEON_SENDER)

void __po_hi_c_driver_serial_leon_init_sender (__po_hi_device_id id)
{
   struct termios             oldtio,newtio;
   __po_hi_c_serial_conf_t*   serialconf;

   __PO_HI_DEBUG_INFO ("[LEON SERIAL] Init sender\n");

   if (serialconf == NULL)
   {
      __PO_HI_DEBUG_INFO ("[LEON SERIAL] Cannot get the name of the device !\n");
      return;
   }

   __po_hi_transport_set_sending_func (id, __po_hi_c_driver_serial_leon_sender);

   if (__po_hi_c_driver_serial_common_get_speed (id) != __PO_HI_DRIVER_SERIAL_COMMON_SPEED_38400)
   {
      __PO_HI_DEBUG_INFO ("[LEON SERIAL] This driver handles only a speed of 38400, exiting initialization !\n");
      return;
   }

   po_hi_c_driver_leon_serial_fd_write = open (serialconf->devname, O_WRONLY );

   if (po_hi_c_driver_leon_serial_fd_write < 0)
   {
      __PO_HI_DEBUG_CRITICAL ("[LEON SERIAL] Error while opening device %s for writing\n", serialconf->devname);
   }
   else
   {
      __PO_HI_DEBUG_DEBUG ("[LEON SERIAL] Device %s successfully opened for writing, fd=%d\n", serialconf->devname, po_hi_c_driver_leon_serial_fd_write);
   }
   tcgetattr (po_hi_c_driver_leon_serial_fd_write, &oldtio); 
   memset (&newtio, '\0', sizeof(newtio));                
        
   newtio.c_cflag |= CREAD ;
   newtio.c_iflag = IGNPAR | IGNBRK;
   newtio.c_lflag |= ICANON;
   newtio.c_cc[VMIN]=1;
   newtio.c_cc[VTIME]=0;
   newtio.c_cflag |= B38400;

   newtio.c_iflag &= ~(IGNBRK | BRKINT | PARMRK | ISTRIP
         | INLCR | IGNCR | ICRNL | IXON);
   newtio.c_oflag &= ~OPOST;
   newtio.c_lflag &= ~(ECHO | ECHONL | ICANON | ISIG | IEXTEN);
   newtio.c_cflag &= ~(CSIZE | PARENB);
   newtio.c_cflag |= CS8;



   if (tcsetattr (po_hi_c_driver_leon_serial_fd_write, TCSANOW, &newtio) == -1)
   {
      __PO_HI_DEBUG_CRITICAL ("[LEON SERIAL] Error in tcsetattr()\n");
   }

   if (tcflush (po_hi_c_driver_leon_serial_fd_write, TCIOFLUSH) == -1)
   {
      __PO_HI_DEBUG_CRITICAL ("[LEON SERIAL] Error in tcflush()\n");
   }


    __PO_HI_DEBUG_INFO ("[LEON SERIAL] End of sender init\n");
}
#endif


#if defined (__PO_HI_NEED_DRIVER_SERIAL_LEON) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LEON_RECEIVER)
void __po_hi_c_driver_serial_leon_init_receiver (__po_hi_device_id id)
{
   struct termios             oldtio,newtio;
   __po_hi_c_serial_conf_t*   serialconf;

   __PO_HI_DEBUG_INFO ("[LEON SERIAL] Init receiver\n");

   serialconf = (__po_hi_c_serial_conf_t*)__po_hi_get_device_configuration (id);


   if (serialconf == NULL)
   {
      __PO_HI_DEBUG_INFO ("[LEON SERIAL] Cannot get the configuration of the device !\n");
      return;
   }

   if (__po_hi_c_driver_serial_common_get_speed (id) != __PO_HI_DRIVER_SERIAL_COMMON_SPEED_38400)
   {
      __PO_HI_DEBUG_INFO ("[LEON SERIAL] This driver handles only a speed of 38400, exiting initialization !\n");
      return;
   }

   po_hi_c_driver_leon_serial_fd_read = open (serialconf->devname, O_RDONLY);

   if (po_hi_c_driver_leon_serial_fd_read < 0)
   {
      __PO_HI_DEBUG_CRITICAL ("[LEON SERIAL] Error while opening device %s for reading\n", serialconf->devname);
   }
   else
   {
      __PO_HI_DEBUG_INFO ("[LEON SERIAL] Device %s successfully opened for receiving, fd=%d\n", serialconf->devname, po_hi_c_driver_leon_serial_fd_read);
   }

   tcgetattr (po_hi_c_driver_leon_serial_fd_read, &oldtio);  /* save current serial port settings */
   tcgetattr (po_hi_c_driver_leon_serial_fd_read, &newtio);  /* save current serial port settings */
   newtio.c_cflag |= CREAD ;
   newtio.c_iflag = IGNPAR | IGNBRK;
   newtio.c_lflag |= ICANON;
   newtio.c_cc[VMIN]=1;
   newtio.c_cc[VTIME]=0;
   newtio.c_cflag |= B38400;
   newtio.c_iflag &= ~(IGNBRK | BRKINT | PARMRK | ISTRIP
         | INLCR | IGNCR | ICRNL | IXON);
   newtio.c_lflag &= ~(ECHO | ECHONL | ICANON | ISIG | IEXTEN);
   newtio.c_cflag &= ~(CSIZE | PARENB);
   newtio.c_cflag |= CS8;

   newtio.c_cflag |= B38400;

   /* 
    * clean the serial line and activate the settings for the port
    */
   if (tcflush (po_hi_c_driver_leon_serial_fd_read, TCIOFLUSH) == -1)
   {
      __PO_HI_DEBUG_CRITICAL ("[LEON SERIAL] Error in tcflush()\n");
   }

   if (tcsetattr (po_hi_c_driver_leon_serial_fd_read, TCSANOW, &newtio) == -1)
   {
      __PO_HI_DEBUG_CRITICAL ("[LEON SERIAL] Error in tcsetattr()\n");
   }

    __PO_HI_DEBUG_INFO ("[LEON SERIAL] End of receiver init\n");
}
#endif


#if defined (__PO_HI_NEED_DRIVER_SERIAL_LEON)

void __po_hi_c_driver_serial_leon_init (__po_hi_device_id id)
{
   __po_hi_c_driver_serial_leon_init_receiver (id);
   __po_hi_c_driver_serial_leon_init_sender (id);
}
#endif


#if defined (__PO_HI_NEED_DRIVER_SERIAL_LEON) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LEON_SENDER)


__po_hi_msg_t __po_hi_c_driver_serial_leon_sender_msg;
int  __po_hi_c_driver_serial_leon_sender (__po_hi_task_id task_id, __po_hi_port_t port)
{
   int n;
   int ts;
   __po_hi_local_port_t local_port;
   __po_hi_request_t*   request;
   __po_hi_port_t       destination_port;

   local_port = __po_hi_get_local_port_from_global_port (port);

   request = __po_hi_gqueue_get_most_recent_value (task_id, local_port);

   destination_port     = __po_hi_gqueue_get_destination (task_id, local_port, 0);

   __po_hi_msg_reallocate (&__po_hi_c_driver_serial_leon_sender_msg);

   request->port = destination_port;

   __po_hi_marshall_request (request, &__po_hi_c_driver_serial_leon_sender_msg);

   n = write (po_hi_c_driver_leon_serial_fd_write, &(__po_hi_c_driver_serial_leon_sender_msg.content[0]), __PO_HI_MESSAGES_MAX_SIZE);

#ifdef __PO_HI_DEBUG_INFO
   __PO_HI_DEBUG_INFO  ("[LEON SERIAL] Message sent: 0x");

   for (ts = 0 ; ts < __PO_HI_MESSAGES_MAX_SIZE ; ts++)
   {
      __PO_HI_DEBUG_INFO ("%x", __po_hi_c_driver_serial_leon_sender_msg.content[ts]);
   }
   __PO_HI_DEBUG_INFO ("\n");
#endif

   return 1;
}
#endif

#endif
