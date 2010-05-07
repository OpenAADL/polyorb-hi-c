/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * Copyright (C) 2010, European Space Agency
 */

#include <drivers/po_hi_driver_linux_serial.h>

#ifdef __PO_HI_NEED_DRIVER_SERIAL_LINUX

#define __PO_HI_DRIVER_SERIAL_LINUX_DEVICE "/dev/ttyS0"
#define __PO_HI_DRIVER_SERIAL_LINUX_BAUDRATE B19200

#include <po_hi_debug.h>
#include <po_hi_utils.h>
#include <po_hi_messages.h>
#include <po_hi_transport.h>
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

int po_hi_c_driver_serial_fd;



void __po_hi_c_driver_serial_linux_poller (void)
{
   unsigned long* swap_pointer;
   unsigned long swap_value;
   __po_hi_msg_t msg;
   __po_hi_request_t request;
   int n;
   int tmp;
   __DEBUGMSG ("Hello, i'm the serial linux poller !\n");
   n = read (po_hi_c_driver_serial_fd, &(msg.content), __PO_HI_MESSAGES_MAX_SIZE); 
   
   if (n == -1)
   {
      __DEBUGMSG("[LINUX SERIAL] Cannot read on socket !\n");
   }


   __DEBUGMSG ("[LINUX SERIAL] read() returns %d\n", n);

   msg.length = n;

   if (n > 0)
   {
      for (tmp = 0 ; tmp < n ; tmp += 4)
      {
         swap_pointer  = (unsigned long*) &msg.content[tmp];
         swap_value    = *swap_pointer;
         *swap_pointer = __po_hi_swap_byte (swap_value);
      }

      printf ("[LINUX SERIAL] Received: %s\n", msg.content);

      __po_hi_unmarshall_request (&request, &msg);

      printf ("[LINUX SERIAL] Destination port: %d\n", request.port);
      __po_hi_main_deliver (&request);
   }
}


void __po_hi_c_driver_serial_linux_init (void)
{
   struct termios oldtio,newtio;

   __DEBUGMSG ("[LINUX SERIAL] Init\n");

   po_hi_c_driver_serial_fd = open(__PO_HI_DRIVER_SERIAL_LINUX_DEVICE, O_RDWR | O_NOCTTY | O_NONBLOCK);

   if (po_hi_c_driver_serial_fd < 0)
   {
      __DEBUGMSG ("[LINUX SERIAL] Error while opening device %s\n", __PO_HI_DRIVER_SERIAL_LINUX_DEVICE);
   }
   else
   {
      __DEBUGMSG ("[LINUX SERIAL] Device successfully opened, fd=%d\n", po_hi_c_driver_serial_fd);
   }

   tcgetattr (po_hi_c_driver_serial_fd, &oldtio);  /* save current serial port settings */
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
   if (tcflush (po_hi_c_driver_serial_fd, TCIOFLUSH) == -1)
   {
      __DEBUGMSG ("[LINUX SERIAL] Error in tcflush()\n");
   }

   if (tcsetattr (po_hi_c_driver_serial_fd, TCSANOW, &newtio) == -1)
   {
      __DEBUGMSG ("[LINUX SERIAL] Error in tcsetattr()\n");
   }

    __DEBUGMSG ("[LINUX SERIAL] End of init\n");
}

int  __po_hi_c_driver_serial_linux_sender (__po_hi_task_id task, __po_hi_port_t port)
{
   write (po_hi_c_driver_serial_fd, "LINUX\n", 6);
   return 1;
}

#endif

