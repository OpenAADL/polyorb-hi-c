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
#include <pci.h>
#include <rasta.h>
#include <apbuart_rasta.h>

/* Rasta includes from GAISLER drivers */

#define __PO_HI_DRIVER_SERIAL_LINUX_DEVICE "/dev/apburasta0"
#define __PO_HI_DRIVER_SERIAL_LINUX_BAUDRATE 19200

int po_hi_c_driver_rasta_serial_fd;

void __po_hi_c_driver_serial_rasta_poller (void)
{
   char buf[1024];
   int n;

   while(1)
   {
      n = read (po_hi_c_driver_rasta_serial_fd, &buf, 1024); 
      __DEBUGMSG ("[RASTA SERIAL] read() returns %d\n", n);
      if (n > 0)
      {
         buf[n] = '\0';
         printf ("[RASTA SERIAL] Received: %s\n", buf);
      }
      sleep(2);
   }
}

void __po_hi_c_driver_serial_rasta_init (void)
{
   __DEBUGMSG ("[RASTA SERIAL] Init\n");
   init_pci();
   __DEBUGMSG ("[RASTA SERIAL] Initializing RASTA ...\n");
  if  ( rasta_register() ){
    __DEBUGMSG(" ERROR !\n");
  }
    __DEBUGMSG(" OK !\n");

  po_hi_c_driver_rasta_serial_fd = open ("/dev/apburasta0", O_RDWR);

   if (po_hi_c_driver_rasta_serial_fd < 0)
   {
      __DEBUGMSG ("[RASTA SERIAL] Error while opening device %s\n", __PO_HI_DRIVER_SERIAL_LINUX_DEVICE);
   }

  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd, APBUART_SET_BAUDRATE, 19200); /* stream mode */
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
   n = write (po_hi_c_driver_rasta_serial_fd, "blabla", 6);
   __DEBUGMSG ("RASTA write returns %d\n", n);
   return 1;
}

#endif

