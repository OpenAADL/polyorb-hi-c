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

#ifdef __PO_HI_NEED_DRIVER_EXARM_NI_6071E_ANALOG

#include <comedilib.h>
#include <po_hi_types.h>

comedi_t *po_hi_driver_exarm_ni_6071e_analog_it;
comedi_range* po_hi_driver_exarm_ni_6071e_analog_range_data1;
comedi_range* po_hi_driver_exarm_ni_6071e_analog_range_data2;
comedi_range* po_hi_driver_exarm_ni_6071e_analog_range_data3;
comedi_range* po_hi_driver_exarm_ni_6071e_analog_range_data4;
comedi_range* po_hi_driver_exarm_ni_6071e_analog_range_data5;
comedi_range* po_hi_driver_exarm_ni_6071e_analog_range_data6;
comedi_range* po_hi_driver_exarm_ni_6071e_analog_range_data7;
comedi_range* po_hi_driver_exarm_ni_6071e_analog_range_data8;
comedi_range* po_hi_driver_exarm_ni_6071e_analog_range_data9;
comedi_range* po_hi_driver_exarm_ni_6071e_analog_range_data10;
comedi_range* po_hi_driver_exarm_ni_6071e_analog_range_data11;
comedi_range* po_hi_driver_exarm_ni_6071e_analog_range_data12;
comedi_range* po_hi_driver_exarm_ni_6071e_analog_range_data13;
comedi_range* po_hi_driver_exarm_ni_6071e_analog_range_data14;
comedi_range* po_hi_driver_exarm_ni_6071e_analog_range_data15;
comedi_range* po_hi_driver_exarm_ni_6071e_analog_range_data16;

lsampl_t po_hi_driver_exarm_ni_6071e_analog_data1;
lsampl_t po_hi_driver_exarm_ni_6071e_analog_data2;
lsampl_t po_hi_driver_exarm_ni_6071e_analog_data3;
lsampl_t po_hi_driver_exarm_ni_6071e_analog_data4;
lsampl_t po_hi_driver_exarm_ni_6071e_analog_data5;
lsampl_t po_hi_driver_exarm_ni_6071e_analog_data6;
lsampl_t po_hi_driver_exarm_ni_6071e_analog_data7;
lsampl_t po_hi_driver_exarm_ni_6071e_analog_data8;
lsampl_t po_hi_driver_exarm_ni_6071e_analog_data9;
lsampl_t po_hi_driver_exarm_ni_6071e_analog_data10;
lsampl_t po_hi_driver_exarm_ni_6071e_analog_data11;
lsampl_t po_hi_driver_exarm_ni_6071e_analog_data12;
lsampl_t po_hi_driver_exarm_ni_6071e_analog_data13;
lsampl_t po_hi_driver_exarm_ni_6071e_analog_data14;
lsampl_t po_hi_driver_exarm_ni_6071e_analog_data15;
lsampl_t po_hi_driver_exarm_ni_6071e_analog_data16;



int po_hi_driver_exarm_ni_6071e_analog_channels[16] = {1,2,3,5,6,7,17,18,19,20,22,24,33,34,35,36};

void __po_hi_c_driver_exarm_ni_6071e_analog_init (__po_hi_device_id device_id)
{
   po_hi_driver_exarm_ni_6071e_analog_it = comedi_open("/dev/comedi0");

   po_hi_driver_exarm_ni_6071e_analog_range_data1 = comedi_get_range (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[0],0);
   po_hi_driver_exarm_ni_6071e_analog_range_data2 = comedi_get_range (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[1],0);
   po_hi_driver_exarm_ni_6071e_analog_range_data3 = comedi_get_range (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[2],0);
   po_hi_driver_exarm_ni_6071e_analog_range_data4 = comedi_get_range (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[3],0);
   po_hi_driver_exarm_ni_6071e_analog_range_data5 = comedi_get_range (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[4],0);
   po_hi_driver_exarm_ni_6071e_analog_range_data6 = comedi_get_range (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[5],0);
   po_hi_driver_exarm_ni_6071e_analog_range_data7 = comedi_get_range (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[6],0);
   po_hi_driver_exarm_ni_6071e_analog_range_data8 = comedi_get_range (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[7],0);
   po_hi_driver_exarm_ni_6071e_analog_range_data9 = comedi_get_range (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[8],0);
   po_hi_driver_exarm_ni_6071e_analog_range_data10 = comedi_get_range (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[9],0);
   po_hi_driver_exarm_ni_6071e_analog_range_data11 = comedi_get_range (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[10],0);
   po_hi_driver_exarm_ni_6071e_analog_range_data12 = comedi_get_range (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[11],0);
   po_hi_driver_exarm_ni_6071e_analog_range_data13 = comedi_get_range (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[12],0);
   po_hi_driver_exarm_ni_6071e_analog_range_data14 = comedi_get_range (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[13],0);
   po_hi_driver_exarm_ni_6071e_analog_range_data15 = comedi_get_range (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[14],0);
   po_hi_driver_exarm_ni_6071e_analog_range_data16 = comedi_get_range (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[15],0);
   return;
}
   
void __po_hi_c_driver_exarm_ni_6071e_analog_poller 
   (double* data1, double* data2, double* data3, double* data4,
    double* data5, double* data6, double* data7, double* data8,
    double* data9, double* data10, double* data11, double* data12,
    double* data13, double* data14, double* data15, double* data16)
{
   comedi_data_read (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[0],0,AREF_GROUND, &po_hi_driver_exarm_ni_6071e_analog_data1);
   comedi_data_read (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[1],0,AREF_GROUND, &po_hi_driver_exarm_ni_6071e_analog_data2);
   comedi_data_read (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[2],0,AREF_GROUND, &po_hi_driver_exarm_ni_6071e_analog_data3);
   comedi_data_read (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[3],0,AREF_GROUND, &po_hi_driver_exarm_ni_6071e_analog_data4);
   comedi_data_read (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[4],0,AREF_GROUND, &po_hi_driver_exarm_ni_6071e_analog_data5);
   comedi_data_read (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[5],0,AREF_GROUND, &po_hi_driver_exarm_ni_6071e_analog_data6);
   comedi_data_read (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[6],0,AREF_GROUND, &po_hi_driver_exarm_ni_6071e_analog_data7);
   comedi_data_read (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[7],0,AREF_GROUND, &po_hi_driver_exarm_ni_6071e_analog_data8);
   comedi_data_read (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[8],0,AREF_GROUND, &po_hi_driver_exarm_ni_6071e_analog_data9);
   comedi_data_read (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[9],0,AREF_GROUND, &po_hi_driver_exarm_ni_6071e_analog_data10);
   comedi_data_read (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[10],0,AREF_GROUND, &po_hi_driver_exarm_ni_6071e_analog_data11);
   comedi_data_read (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[11],0,AREF_GROUND, &po_hi_driver_exarm_ni_6071e_analog_data12);
   comedi_data_read (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[12],0,AREF_GROUND, &po_hi_driver_exarm_ni_6071e_analog_data13);
   comedi_data_read (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[13],0,AREF_GROUND, &po_hi_driver_exarm_ni_6071e_analog_data14);
   comedi_data_read (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[14],0,AREF_GROUND, &po_hi_driver_exarm_ni_6071e_analog_data15);
   comedi_data_read (po_hi_driver_exarm_ni_6071e_analog_it,0,po_hi_driver_exarm_ni_6071e_analog_channels[15],0,AREF_GROUND, &po_hi_driver_exarm_ni_6071e_analog_data16);

   *data1 = comedi_to_phys (po_hi_driver_exarm_ni_6071e_analog_data1, po_hi_driver_exarm_ni_6071e_analog_range_data1, 4095);
   *data2 = comedi_to_phys (po_hi_driver_exarm_ni_6071e_analog_data2, po_hi_driver_exarm_ni_6071e_analog_range_data2, 4095);
   *data3 = comedi_to_phys (po_hi_driver_exarm_ni_6071e_analog_data3, po_hi_driver_exarm_ni_6071e_analog_range_data3, 4095);
   *data4 = comedi_to_phys (po_hi_driver_exarm_ni_6071e_analog_data4, po_hi_driver_exarm_ni_6071e_analog_range_data4, 4095);
   *data5 = comedi_to_phys (po_hi_driver_exarm_ni_6071e_analog_data5, po_hi_driver_exarm_ni_6071e_analog_range_data5, 4095);
   *data6 = comedi_to_phys (po_hi_driver_exarm_ni_6071e_analog_data6, po_hi_driver_exarm_ni_6071e_analog_range_data6, 4095);
   *data7 = comedi_to_phys (po_hi_driver_exarm_ni_6071e_analog_data7, po_hi_driver_exarm_ni_6071e_analog_range_data7, 4095);
   *data8 = comedi_to_phys (po_hi_driver_exarm_ni_6071e_analog_data8, po_hi_driver_exarm_ni_6071e_analog_range_data8, 4095);
   *data9 = comedi_to_phys (po_hi_driver_exarm_ni_6071e_analog_data9, po_hi_driver_exarm_ni_6071e_analog_range_data9, 4095);
   *data10 = comedi_to_phys (po_hi_driver_exarm_ni_6071e_analog_data10, po_hi_driver_exarm_ni_6071e_analog_range_data10, 4095);
   *data11 = comedi_to_phys (po_hi_driver_exarm_ni_6071e_analog_data11, po_hi_driver_exarm_ni_6071e_analog_range_data11, 4095);
   *data12 = comedi_to_phys (po_hi_driver_exarm_ni_6071e_analog_data12, po_hi_driver_exarm_ni_6071e_analog_range_data12, 4095);
   *data13 = comedi_to_phys (po_hi_driver_exarm_ni_6071e_analog_data13, po_hi_driver_exarm_ni_6071e_analog_range_data13, 4095);
   *data14 = comedi_to_phys (po_hi_driver_exarm_ni_6071e_analog_data14, po_hi_driver_exarm_ni_6071e_analog_range_data14, 4095);
   *data15 = comedi_to_phys (po_hi_driver_exarm_ni_6071e_analog_data15, po_hi_driver_exarm_ni_6071e_analog_range_data15, 4095);
   *data16 = comedi_to_phys (po_hi_driver_exarm_ni_6071e_analog_data16, po_hi_driver_exarm_ni_6071e_analog_range_data16, 4095);
   return;
}

#endif
