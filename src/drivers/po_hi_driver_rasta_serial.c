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

#include <po_hi_debug.h>
#include <drivers/rtems_utils.h>
#include <drivers/po_hi_driver_rasta_serial.h>

#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>
/* POSIX-style files */

#include <pci.h>
#include <rasta.h>
#include <apbuart_rasta.h>

/* Rasta includes from GAISLER drivers */

#define __PO_HI_DRIVER_SERIAL_RASTA_DEVICE "/dev/apburasta0"
#define __PO_HI_DRIVER_SERIAL_RASTA_BAUDRATE 19200

int po_hi_c_driver_rasta_serial_fd;

void __po_hi_c_driver_serial_rasta_poller (void)
{
   char buf[1024];
   int n;
   __DEBUGMSG ("Hello, i'm the serial RASTA poller !\n");
   n = read (po_hi_c_driver_rasta_serial_fd, &buf, 6); 
   __DEBUGMSG ("[RASTA SERIAL] read() returns %d\n", n);
   if (n > 0)
   {
      buf[n] = '\0';
      printf ("[RASTA SERIAL] Received: %s\n", buf);
   }
}

void __po_hi_c_driver_serial_rasta_init (void)
{
   __DEBUGMSG ("[RASTA SERIAL] Init\n");
   init_pci();
   __DEBUGMSG ("[RASTA SERIAL] Initializing RASTA ...\n");
  if  ( rasta_register() ){
    __DEBUGMSG(" ERROR !\n");
    return;
  }
    __DEBUGMSG(" OK !\n");

  po_hi_c_driver_rasta_serial_fd = open (__PO_HI_DRIVER_SERIAL_RASTA_DEVICE, O_RDWR);

   if (po_hi_c_driver_rasta_serial_fd < 0)
   {
      __DEBUGMSG ("[RASTA SERIAL] Error while opening device %s\n", __PO_HI_DRIVER_SERIAL_RASTA_DEVICE);
   }

  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd, APBUART_SET_BAUDRATE, __PO_HI_DRIVER_SERIAL_RASTA_BAUDRATE); /* stream mode */
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd, APBUART_SET_BLOCKING, APBUART_BLK_RX | APBUART_BLK_TX | APBUART_BLK_FLUSH);
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd, APBUART_SET_TXFIFO_LEN, 64);  /* Transmitt buffer 64 chars */
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd, APBUART_SET_RXFIFO_LEN, 256); /* Receive buffer 256 chars */
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd, APBUART_SET_ASCII_MODE, 0); /* Make \n go \n\r or \r\n */
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd, APBUART_CLR_STATS, 0);
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd, APBUART_START, 0);
}

int __po_hi_c_driver_serial_rasta_sender (const __po_hi_task_id task_id, const __po_hi_port_t port)
{
   int n;
   __po_hi_local_port_t local_port;

   local_port = __po_hi_port_global_to_local[(int)port];
   request = &(__po_hi_gqueues_most_recent_values[id][local_port]);
   n = write (po_hi_c_driver_rasta_serial_fd, "blabl\n", 6);
   __DEBUGMSG ("RASTA write returns %d\n", n);
   return 1;
}

#endif

