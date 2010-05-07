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

#include <marshallers.h>

#include <po_hi_debug.h>
#include <po_hi_transport.h>
#include <po_hi_gqueue.h>
#include <po_hi_messages.h>
#include <drivers/rtems_utils.h>
#include <drivers/po_hi_driver_rasta_spacewire.h>

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

int po_hi_c_driver_rasta_spacewire_fd;

void __po_hi_c_driver_spacewire_rasta_poller (void)
{
   __DEBUGMSG ("[RASTA SPACEWIRE] Hello, i'm the poller !\n");
}

void __po_hi_c_driver_spacewire_rasta_init (void)
{
   __DEBUGMSG ("[RASTA SPACEWIRE] Init\n");
   init_pci();
   __DEBUGMSG ("[RASTA SPACEWIRE] Initializing RASTA ...\n");
  if  ( rasta_register() ){
    __DEBUGMSG(" ERROR !\n");
    return;
  }
    __DEBUGMSG(" OK !\n");
}

int __po_hi_c_driver_spacewire_rasta_sender (const __po_hi_task_id task_id, const __po_hi_port_t port)
{
   (void) task_id;
   (void) port;
   return 1;
}

#endif /* __PO_HI_NEED_DRIVER_SPACEWIRE_RASTA */


