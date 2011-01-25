/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2011, European Space Agency (ESA).
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

void __po_hi_c_driver_serial_leon_poller (void)
{
   int n;
   int ts;
   int tr;

   unsigned long* swap_pointer;
   unsigned long swap_value;

   __po_hi_msg_t msg;
   __po_hi_request_t request;

   __PO_HI_DEBUG_DEBUG ("[LEON SERIAL] Hello, i'm the serial poller , must read %d bytes!\n", __PO_HI_MESSAGES_MAX_SIZE);

   __po_hi_msg_reallocate (&msg);


   tr = 0; 

   while (tr < __PO_HI_MESSAGES_MAX_SIZE)
   {
      n = read (po_hi_c_driver_leon_serial_fd_read, &(msg.content[tr]), 1); 
      if (n == -1)
      {
         __PO_HI_DEBUG_CRITICAL ("[LEON SERIAL] Cannot read on serial\n");
      }
      if (n == 1)
      {
         tr++;
      }
   }

#ifdef __PO_HI_DEBUG_INFO
   __PO_HI_DEBUG_INFO  ("[LEON SERIAL] Message: 0x");

   for (ts = 0 ; ts < __PO_HI_MESSAGES_MAX_SIZE ; ts++)
   {
      __PO_HI_DEBUG_INFO ("%x", msg.content[ts]);
   }
   __PO_HI_DEBUG_INFO ("\n");
#endif
   

   if (tr != __PO_HI_MESSAGES_MAX_SIZE)
   {
      __PO_HI_DEBUG_CRITICAL ("[LEON SERIAL] Inconsistent received message size (received %d bytes)!\n", n);
   }

   __PO_HI_DEBUG_DEBUG ("[LEON SERIAL] read() syscall returns in total %d\n", tr);

   msg.length = n;
   swap_pointer  = (unsigned long*) &msg.content[0];
   swap_value    = *swap_pointer;
   *swap_pointer = __po_hi_swap_byte (swap_value);

#ifdef __PO_HI_DEBUG_INFO
   __PO_HI_DEBUG_INFO ("[LEON SERIAL] Message after swapped port: 0x");
   for (ts = 0 ; ts < msg.length ; ts++)
   {
        __PO_HI_DEBUG_INFO ("%x", msg.content[ts]);
   }
   __PO_HI_DEBUG_INFO ("\n");

   __PO_HI_DEBUG_INFO ("[LEON SERIAL] Received: %s\n", msg.content);
#endif

   __po_hi_unmarshall_request (&request, &msg);

   if (request.port > __PO_HI_NB_PORTS)
   {
      __PO_HI_DEBUG_WARNING ("[LEON SERIAL] Invalid port number !\n");
      return;
   }

   __PO_HI_DEBUG_INFO ("[LEON SERIAL] Destination port: %d\n", request.port);
   __po_hi_main_deliver (&request);
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

   if (__po_hi_c_driver_serial_common_get_speed (id) != __PO_HI_DRIVER_SERIAL_COMMON_SPEED_38400)
   {
      __PO_HI_DEBUG_INFO ("[LEON SERIAL] This driver handles only a speed of 38400, exiting initialization !\n");
      return;
   }

   po_hi_c_driver_leon_serial_fd_write = open (serialconf->devname, O_WRONLY );

   if (po_hi_c_driver_leon_serial_fd_write < 0)
   {
      __PO_HI_DEBUG_CRITICAL ("[LEON SERIAL] Error while opening device %s\n", serialconf->devname);
   }
   else
   {
      __PO_HI_DEBUG_DEBUG ("[LEON SERIAL] Device %s successfully opened, fd=%d\n", serialconf->devname, po_hi_c_driver_leon_serial_fd_write);
   }

   tcgetattr (po_hi_c_driver_leon_serial_fd_write, &oldtio);  /* save current serial port settings */
   memset (&newtio, '\0', sizeof(newtio));                /* clear struct for new port settings */
        
   /* 
    * BAUDRATE: Set bps rate. You could also use cfsetispeed and cfsetospeed.
    * CRTSCTS : output hardware flow control (only used if the cable has
    *           all necessary lines. See sect. 7 of Serial-HOWTO)
    * CS8     : 8n1 (8bit,no parity,1 stopbit)
    * CLOCAL  : local connection, no modem contol
    * CREAD   : enable receiving characters
    */

   newtio.c_cflag = CRTSCTS | CS8 | CLOCAL;
   /* 
    *  IGNPAR  : ignore bytes with parity errors
    *  ICRNL   : map CR to NL (otherwise a CR input on the other computer
    *            will not terminate input) otherwise make device raw 
    *            (no other input processing)
    */
   newtio.c_iflag = IGNPAR | ICRNL;
         
   /*
    * Raw output.
    */
   newtio.c_oflag = OCRNL;
         
   /*
    * ICANON  : enable canonical input
    * disable all echo functionality, and don't send signals to calling program
   newtio.c_lflag = ICANON;
    */
   newtio.c_lflag = ~( ICANON | ECHO | ECHONL | ECHOK | ECHOE | ECHOPRT | ECHOCTL );
   newtio.c_cc[VMIN] = 5;
   newtio.c_cc[VTIME] = 20;


   if (tcsetattr (po_hi_c_driver_leon_serial_fd_write, TCSANOW, &newtio) == -1)
   {
      __PO_HI_DEBUG_CRITICAL ("[LEON SERIAL] Error in tcsetattr()\n");
   }

   /* 
    * clean the serial line and activate the settings for the port
    */
   if (tcflush (po_hi_c_driver_leon_serial_fd_write, TCIOFLUSH) == -1)
   {
      __PO_HI_DEBUG_CRITICAL ("[LEON SERIAL] Error in tcflush()\n");
   }


    __PO_HI_DEBUG_INFO ("[LEON SERIAL] End of init\n");
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

   po_hi_c_driver_leon_serial_fd_read = open (serialconf->devname, O_RDONLY | O_NOCTTY);

   if (po_hi_c_driver_leon_serial_fd_read < 0)
   {
      __PO_HI_DEBUG_CRITICAL ("[LEON SERIAL] Error while opening device %s\n", serialconf->devname);
   }
   else
   {
      __PO_HI_DEBUG_INFO ("[LEON SERIAL] Device successfully opened, fd=%d\n", po_hi_c_driver_leon_serial_fd_read);
   }

   tcgetattr (po_hi_c_driver_leon_serial_fd_read, &oldtio);  /* save current serial port settings */
   memset (&newtio, '\0', sizeof(newtio));                /* clear struct for new port settings */
        
   /* 
    * BAUDRATE: Set bps rate. You could also use cfsetispeed and cfsetospeed.
    * CRTSCTS : output hardware flow control (only used if the cable has
    *           all necessary lines. See sect. 7 of Serial-HOWTO)
    * CS8     : 8n1 (8bit,no parity,1 stopbit)
    * CLOCAL  : local connection, no modem contol
    * CREAD   : enable receiving characters
    */

   newtio.c_cflag = CRTSCTS | CS8 | CLOCAL | CREAD;
         
   /*
    *  IGNPAR  : ignore bytes with parity errors
    *  ICRNL   : map CR to NL (otherwise a CR input on the other computer
    *            will not terminate input) otherwise make device raw 
    *            (no other input processing)
   newtio.c_iflag = IGNPAR | ICRNL;
    */
         
   /*
    * Raw output.
    */
   newtio.c_oflag = 1;
         
   /*
    * ICANON  : enable canonical input
    * disable all echo functionality, and don't send signals to calling program
   newtio.c_lflag = ICANON;
    */

   /* 
    * Initialize all control characters 
    * default values can be found in /usr/include/termios.h, and are given
    * in the comments, but we don't need them here.
    */

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

    __PO_HI_DEBUG_INFO ("[LEON SERIAL] End of init\n");
}
#endif


#if defined (__PO_HI_NEED_DRIVER_SERIAL_LEON)

void __po_hi_c_driver_serial_leon_init (__po_hi_device_id id)
{
   struct                     termios oldtio,newtio;
   __po_hi_c_serial_conf_t*   serialconf;

   __PO_HI_DEBUG_INFO ("[LEON SERIAL] Init both sender and receiver\n");

   serialconf = (__po_hi_c_serial_conf_t*)__po_hi_get_device_configuration (id);

   if (serialconf == NULL)
   {
      __PO_HI_DEBUG_INFO ("[LEON SERIAL] Cannot get the name of the device !\n");
      return;
   }

   if (__po_hi_c_driver_serial_common_get_speed (id) != __PO_HI_DRIVER_SERIAL_COMMON_SPEED_38400)
   {
      __PO_HI_DEBUG_INFO ("[LEON SERIAL] This driver handles only a speed of 38400, exiting initialization !\n");
      return;
   }

   po_hi_c_driver_leon_serial_fd_read = po_hi_c_driver_leon_serial_fd_write = open( serialconf->devname, O_RDWR | O_NOCTTY | O_NONBLOCK);

   if (po_hi_c_driver_leon_serial_fd_read < 0)
   {
      __PO_HI_DEBUG_CRITICAL ("[LEON SERIAL] Error while opening device %s\n", serialconf->devname);
   }
   else
   {
      __PO_HI_DEBUG_INFO ("[LEON SERIAL] Device successfully opened, fd=%d\n", po_hi_c_driver_leon_serial_fd_read);
   }

   tcgetattr (po_hi_c_driver_leon_serial_fd_read, &oldtio);  /* save current serial port settings */
   memset (&newtio, '\0', sizeof(newtio));                /* clear struct for new port settings */
        
   /* 
    * BAUDRATE: Set bps rate. You could also use cfsetispeed and cfsetospeed.
    * CRTSCTS : output hardware flow control (only used if the cable has
    *           all necessary lines. See sect. 7 of Serial-HOWTO)
    * CS8     : 8n1 (8bit,no parity,1 stopbit)
    * CLOCAL  : local connection, no modem contol
    * CREAD   : enable receiving characters
    */

   newtio.c_cflag = CRTSCTS | CS8 | CLOCAL | CREAD;
         
   /*
    *  IGNPAR  : ignore bytes with parity errors
    *  ICRNL   : map CR to NL (otherwise a CR input on the other computer
    *            will not terminate input) otherwise make device raw 
    *            (no other input processing)
    */
   newtio.c_iflag = IGNPAR | ICRNL;
         
   /*
    * Raw output.
    */
   newtio.c_oflag = 1;
         
   /*
    * ICANON  : enable canonical input
    * disable all echo functionality, and don't send signals to calling program
    */
   newtio.c_lflag = ICANON;

   /* 
    * Initialize all control characters 
    * default values can be found in /usr/include/termios.h, and are given
    * in the comments, but we don't need them here.
    */
   newtio.c_cc[VINTR]    = 0;     /* Ctrl-c */ 
   newtio.c_cc[VQUIT]    = 0;     /* Ctrl-\ */
   newtio.c_cc[VERASE]   = 0;     /* del */
   newtio.c_cc[VKILL]    = 0;     /* @ */
   newtio.c_cc[VEOF]     = 4;     /* Ctrl-d */
   newtio.c_cc[VTIME]    = 0;     /* inter-character timer unused */
   newtio.c_cc[VMIN]     = 1;     /* blocking read until 1 character arrives */
   newtio.c_cc[VSWTC]    = 0;     /* '\0' */
   newtio.c_cc[VSTART]   = 0;     /* Ctrl-q */ 
   newtio.c_cc[VSTOP]    = 0;     /* Ctrl-s */
   newtio.c_cc[VSUSP]    = 0;     /* Ctrl-z */
   newtio.c_cc[VEOL]     = 0;     /* '\0' */
   newtio.c_cc[VREPRINT] = 0;     /* Ctrl-r */
   newtio.c_cc[VDISCARD] = 0;     /* Ctrl-u */
   newtio.c_cc[VWERASE]  = 0;     /* Ctrl-w */
   newtio.c_cc[VLNEXT]   = 0;     /* Ctrl-v */
   newtio.c_cc[VEOL2]    = 0;     /* '\0' */

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

    __PO_HI_DEBUG_INFO ("[LEON SERIAL] End of init\n");
}
#endif


#if defined (__PO_HI_NEED_DRIVER_SERIAL_LEON) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LEON_SENDER)

int  __po_hi_c_driver_serial_leon_sender (__po_hi_task_id task_id, __po_hi_port_t port)
{
   int n;
   int ts;
   unsigned long* swap_pointer;
   unsigned long swap_value;
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

   /* Swap only the port (first 32 bytes) */
   swap_pointer  = (unsigned long*) &msg.content[0];
   swap_value    = *swap_pointer;
   *swap_pointer = __po_hi_swap_byte (swap_value);

   n = write (po_hi_c_driver_leon_serial_fd_write, &msg, __PO_HI_MESSAGES_MAX_SIZE);

#ifdef __PO_HI_DEBUG_INFO
   __PO_HI_DEBUG_INFO  ("[LEON SERIAL] Message sent: 0x");

   for (ts = 0 ; ts < __PO_HI_MESSAGES_MAX_SIZE ; ts++)
   {
      __PO_HI_DEBUG_INFO ("%x", msg.content[ts]);
   }
   __PO_HI_DEBUG_INFO ("\n");
#endif

   return 1;
}
#endif

#endif
