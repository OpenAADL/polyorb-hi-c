/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * Copyright (C) 2010, European Space Agency
 */

#include <deployment.h>
/* Generated code header */

#if ((defined __PO_HI_NEED_DRIVER_SPACEWIRE_RASTA) || \
     (defined __PO_HI_NEED_DRIVER_SERIAL_RASTA))

#include <pci.h>
#include <rasta.h>
#include <apbuart_rasta.h>
/* Rasta includes from GAISLER drivers */

#include <po_hi_debug.h>
/* PolyORB-HI-C includes */

int __po_hi_c_driver_rasta_common_is_init = 0;

void __po_hi_c_driver_rasta_common_init ()
{
   if (__po_hi_c_driver_rasta_common_is_init == 1)
   {
      return;
   }

   __DEBUGMSG ("[RASTA SERIAL] Init\n");
   init_pci();
   __DEBUGMSG ("[RASTA SERIAL] Initializing RASTA ...\n");
  if  ( rasta_register() ){
    __DEBUGMSG(" ERROR !\n");
    return;
  }
    __DEBUGMSG(" OK !\n");

   __po_hi_c_driver_rasta_common_is_init = 1;

}

#endif

