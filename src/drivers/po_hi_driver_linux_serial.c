/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * Copyright (C) 2010, European Space Agency
 */

#include <drivers/po_hi_driver_linux_serial.h>

#if defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX_SENDER) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX_RECEIVER)

#define __PO_HI_DRIVER_SERIAL_LINUX_BAUDRATE B19200

#include <po_hi_debug.h>
#include <po_hi_utils.h>
#include <po_hi_messages.h>
#include <po_hi_transport.h>
#include <po_hi_gqueue.h>
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
#include <strings.h>
/* Linux-specific files */

int po_hi_c_driver_serial_fd_read;
int po_hi_c_driver_serial_fd_write;

#if defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX_RECEIVER)

void __po_hi_c_driver_serial_linux_poller (void)
{
   int n;
   int ts;

   unsigned long* swap_pointer;
   unsigned long swap_value;

   __po_hi_msg_t msg;
   __po_hi_request_t request;

   __DEBUGMSG ("[LINUX SERIAL] Hello, i'm the serial poller , must read %d bytes!\n", __PO_HI_MESSAGES_MAX_SIZE);

   __po_hi_msg_reallocate (&msg);

   n = read (po_hi_c_driver_serial_fd_read, &(msg.content[0]), __PO_HI_MESSAGES_MAX_SIZE); 

   __DEBUGMSG  ("[LINUX SERIAL] Message: 0x");

   for (ts = 0 ; ts < __PO_HI_MESSAGES_MAX_SIZE ; ts++)
   {
      __DEBUGMSG ("%x", msg.content[ts]);
   }
   __DEBUGMSG ("\n");
   
   if (n == -1)
   {
      __DEBUGMSG("[LINUX SERIAL] Cannot read on socket !\n");
      return;
   }

   if (n == 0)
   {
      return;
   }


   __DEBUGMSG ("[LINUX SERIAL] read() returns %d\n", n);

   msg.length = n;

   swap_pointer  = (unsigned long*) &msg.content[0];
   swap_value    = *swap_pointer;
   *swap_pointer = __po_hi_swap_byte (swap_value);

   __DEBUGMSG  ("[LINUX SERIAL] Message after swapped port: 0x");
   for (ts = 0 ; ts < msg.length ; ts++)
   {
        __DEBUGMSG ("%x", msg.content[ts]);
   }
   __DEBUGMSG ("\n");

   __DEBUGMSG ("[LINUX SERIAL] Received: %s\n", msg.content);

   __po_hi_unmarshall_request (&request, &msg);

   __DEBUGMSG ("[LINUX SERIAL] Destination port: %d\n", request.port);
   __po_hi_main_deliver (&request);
}
#endif


#if defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX_SENDER)

void __po_hi_c_driver_serial_linux_init_sender (__po_hi_device_id id)
{
   struct termios oldtio,newtio;

   __DEBUGMSG ("[LINUX SERIAL] Init\n");

   po_hi_c_driver_serial_fd_write = open( __po_hi_get_device_naming (id), O_RDWR | O_NOCTTY | O_NONBLOCK);

   if (po_hi_c_driver_serial_fd_write < 0)
   {
      __DEBUGMSG ("[LINUX SERIAL] Error while opening device %s\n", __po_hi_get_device_naming (id));
   }
   else
   {
      __DEBUGMSG ("[LINUX SERIAL] Device successfully opened, fd=%d\n", po_hi_c_driver_serial_fd_write);
   }

   tcgetattr (po_hi_c_driver_serial_fd_write, &oldtio);  /* save current serial port settings */
   bzero (&newtio, sizeof(newtio));                /* clear struct for new port settings */
        
   /* 
    * BAUDRATE: Set bps rate. You could also use cfsetispeed and cfsetospeed.
    * CRTSCTS : output hardware flow control (only used if the cable has
    *           all necessary lines. See sect. 7 of Serial-HOWTO)
    * CS8     : 8n1 (8bit,no parity,1 stopbit)
    * CLOCAL  : local connection, no modem contol
    * CREAD   : enable receiving characters
    */

   newtio.c_cflag = __PO_HI_DRIVER_SERIAL_LINUX_BAUDRATE | CRTSCTS | CS8 | CLOCAL | CREAD;
         
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
   if (tcflush (po_hi_c_driver_serial_fd_write, TCIOFLUSH) == -1)
   {
      __DEBUGMSG ("[LINUX SERIAL] Error in tcflush()\n");
   }

   if (tcsetattr (po_hi_c_driver_serial_fd_write, TCSANOW, &newtio) == -1)
   {
      __DEBUGMSG ("[LINUX SERIAL] Error in tcsetattr()\n");
   }

    __DEBUGMSG ("[LINUX SERIAL] End of init\n");
}
#endif


#if defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX_RECEIVER)
void __po_hi_c_driver_serial_linux_init_receiver (__po_hi_device_id id)
{
   struct termios oldtio,newtio;

   __DEBUGMSG ("[LINUX SERIAL] Init\n");

   po_hi_c_driver_serial_fd_read = open( __po_hi_get_device_naming (id), O_RDONLY | O_NOCTTY);

   if (po_hi_c_driver_serial_fd_read < 0)
   {
      __DEBUGMSG ("[LINUX SERIAL] Error while opening device %s\n", __po_hi_get_device_naming (id));
   }
   else
   {
      __DEBUGMSG ("[LINUX SERIAL] Device successfully opened, fd=%d\n", po_hi_c_driver_serial_fd_read);
   }

   tcgetattr (po_hi_c_driver_serial_fd_read, &oldtio);  /* save current serial port settings */
   bzero (&newtio, sizeof(newtio));                /* clear struct for new port settings */
        
   /* 
    * BAUDRATE: Set bps rate. You could also use cfsetispeed and cfsetospeed.
    * CRTSCTS : output hardware flow control (only used if the cable has
    *           all necessary lines. See sect. 7 of Serial-HOWTO)
    * CS8     : 8n1 (8bit,no parity,1 stopbit)
    * CLOCAL  : local connection, no modem contol
    * CREAD   : enable receiving characters
    */

   newtio.c_cflag = __PO_HI_DRIVER_SERIAL_LINUX_BAUDRATE | CRTSCTS | CS8 | CLOCAL | CREAD;
         
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
   if (tcflush (po_hi_c_driver_serial_fd_read, TCIOFLUSH) == -1)
   {
      __DEBUGMSG ("[LINUX SERIAL] Error in tcflush()\n");
   }

   if (tcsetattr (po_hi_c_driver_serial_fd_read, TCSANOW, &newtio) == -1)
   {
      __DEBUGMSG ("[LINUX SERIAL] Error in tcsetattr()\n");
   }

    __DEBUGMSG ("[LINUX SERIAL] End of init\n");
}
#endif


#if defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX)

void __po_hi_c_driver_serial_linux_init (__po_hi_device_id id)
{
   struct termios oldtio,newtio;

   __DEBUGMSG ("[LINUX SERIAL] Init\n");

   po_hi_c_driver_serial_fd_read = po_hi_c_driver_serial_fd_write = open( __po_hi_get_device_naming (id), O_RDWR | O_NOCTTY | O_NONBLOCK);

   if (po_hi_c_driver_serial_fd_read < 0)
   {
      __DEBUGMSG ("[LINUX SERIAL] Error while opening device %s\n", __po_hi_get_device_naming (id));
   }
   else
   {
      __DEBUGMSG ("[LINUX SERIAL] Device successfully opened, fd=%d\n", po_hi_c_driver_serial_fd_serial);
   }

   tcgetattr (po_hi_c_driver_serial_fd_read, &oldtio);  /* save current serial port settings */
   bzero (&newtio, sizeof(newtio));                /* clear struct for new port settings */
        
   /* 
    * BAUDRATE: Set bps rate. You could also use cfsetispeed and cfsetospeed.
    * CRTSCTS : output hardware flow control (only used if the cable has
    *           all necessary lines. See sect. 7 of Serial-HOWTO)
    * CS8     : 8n1 (8bit,no parity,1 stopbit)
    * CLOCAL  : local connection, no modem contol
    * CREAD   : enable receiving characters
    */

   newtio.c_cflag = __PO_HI_DRIVER_SERIAL_LINUX_BAUDRATE | CRTSCTS | CS8 | CLOCAL | CREAD;
         
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
   if (tcflush (po_hi_c_driver_serial_fd_read, TCIOFLUSH) == -1)
   {
      __DEBUGMSG ("[LINUX SERIAL] Error in tcflush()\n");
   }

   if (tcsetattr (po_hi_c_driver_serial_fd_read, TCSANOW, &newtio) == -1)
   {
      __DEBUGMSG ("[LINUX SERIAL] Error in tcsetattr()\n");
   }

    __DEBUGMSG ("[LINUX SERIAL] End of init\n");
}
#endif


#if defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX) || \
    defined (__PO_HI_NEED_DRIVER_SERIAL_LINUX_SENDER)

int  __po_hi_c_driver_serial_linux_sender (__po_hi_task_id task_id, __po_hi_port_t port)
{
   int n;
   int tmp;
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

   n = write (po_hi_c_driver_serial_fd_write, &msg, __PO_HI_MESSAGES_MAX_SIZE);

   __DEBUGMSG  ("[LINUX SERIAL] Message sent: 0x");

   for (ts = 0 ; ts < __PO_HI_MESSAGES_MAX_SIZE ; ts++)
   {
      __DEBUGMSG ("%x", msg.content[ts]);
   }
   __DEBUGMSG ("\n");

   return 1;
}
#endif

#endif

