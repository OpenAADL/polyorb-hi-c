/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * Copyright (C) 2010, European Space Agency
 */

#include <drivers/po_hi_driver_linux_serial.h>

#ifdef __PO_HI_NEED_SERIAL_LINUX

#include <stdio.h>

void __po_hi_c_driver_serial_linux_poller (void)
{
      printf ("Hello, i'm the serial linux poller !\n");
}


void __po_hi_c_driver_serial_linux_init (void)
{
      printf ("Hello, i'm the serial driver, i'm initializing the whole thing\n");
}

#endif

