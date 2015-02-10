/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2012-2014 ESA & ISAE.
 */

#include <deployment.h>

#ifdef __PO_HI_NEED_DRIVER_EXARM_NI_6071E_DIGITAL

#include <comedilib.h>
#include <po_hi_types.h>
#include <po_hi_debug.h>

comedi_t *po_hi_driver_exarm_ni_6071e_digital_it;

void __po_hi_c_driver_exarm_ni_6071e_digital_init (__po_hi_device_id device_id)
{
   int ret;

   po_hi_driver_exarm_ni_6071e_digital_it = comedi_open("/dev/comedi0");

   ret = comedi_dio_config(po_hi_driver_exarm_ni_6071e_digital_it, 2, 1, COMEDI_INPUT);

   if (ret == -1)
   {
      __DEBUGMSG ("Error when invoking comedi_dio_config()");
   }

   ret = comedi_dio_config(po_hi_driver_exarm_ni_6071e_digital_it, 2, 0, COMEDI_INPUT);

   if (ret == -1)
   {
      __DEBUGMSG ("Error when invoking comedi_dio_config()");
   }

   return;
}
 

void __po_hi_c_driver_exarm_ni_6071e_digital_poller (unsigned int* data1, unsigned int* data2)
{
   comedi_dio_read(po_hi_driver_exarm_ni_6071e_digital_it, 2, 1, (unsigned int*)data1);
   comedi_dio_read(po_hi_driver_exarm_ni_6071e_digital_it, 2, 0, (unsigned int*)data2);
   return;
}

#endif
