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

#ifdef __PO_HI_NEED_DRIVER_XC4V_FPGA
#include <stdio.h>
#include <pci.h>
#include <ambapp.h>
#include <rasta.h>

#define __PO_HI_DRIVER_XC4V_VENDOR_ID    0x1AC8
#define __PO_HI_DRIVER_XC4V_DEVICE_ID    0x0054

#define  __PO_HI_DRIVER_XC4V_INIT_FPGA if(__po_hi_driver_xc4v_fpga_init==0){Initialize_ESA_FPGA();__po_hi_driver_x4cv_fpga_init=1;}


unsigned             __po_hi_driver_xc4v_drv_addr;
unsigned int         __po_hi_driver_xc4v_bar0;
int                  __po_hi_driver_xc4v_fpga_init = 0;
LEON_Register_Map   *__po_hi_driver_xc4v_fpga_regs = (LEON_Register_Map *)0x80000000;

void set_page0_register (unsigned v)
{
   unsigned int *page0 = NULL;
   page0 = (unsigned int *)__po_hi_driver_xc4v_bar0;
   *page0 = v;
}


void set_page1_register (unsigned apb_offset, unsigned v)
{
   unsigned* page1; 
   page1 = (unsigned*) (__po_hi_driver_xc4v_bar0 + apb_offset + 0x10);
   *page1 = v;
}


void set_grpci_mmap (unsigned apb_offset, unsigned v)
{
   unsigned* grpci;
   grpci = (unsigned*) (__po_hi_driver_xc4v_bar0 +  apb_offset);
   *grpci = v;
}

void configure_ioports ()
{
   __po_hi_driver_xc4v_fpga_regs->PIO_Direction &= ~(1<<7);
   __po_hi_driver_xc4v_fpga_regs->PIO_Interrupt |= (0x87<<8);     /* level sensitive */
}


int __po_hi_driver_xc4v_fpga_initialize() 
{
   int ret;
   int instance = 0;
   int pbus = 0;
   int pdev = 0;
   int pfun = 0;

   init_pci ();

   ret = BSP_pciFindDevice (__PO_HI_DRIVER_XC4V_VENDOR_ID, __PO_HI_DRIVER_XC4V_DEVICE_ID, instance, &pbus, &pdev, &pfun);

   if (ret != 0)
   {
      __DEBUGMSG ("Device not found, return =%d\n");
      return 0;
   }
   else
   {
      __DEBUGMSG ("Device found, bus=0x%x, dev=0x%x, fun=0x%x\n", pbus, pdev, pfun);
   }

   pci_read_config_dword(pbus, pdev, pfun, 0x10, &__po_hi_driver_xc4v_bar0);

   __DEBUGMSG ("Configuration, bar0=0x%x\n", __po_hi_driver_xc4v_bar0);

   /* 
    * The three lines above are equivalent to the Configure_XC4V 
    * Ada procedure
    */
   __po_hi_driver_xc4v_fpga_set_page0_register (0x80000000);
   __po_hi_driver_xc4v_fpga_set_grpci_mmap (0x400, 0x40000000);
   __po_hi_driver_xc4v_fpga_set_page1_register (0x400, 0x40000000);

   /* 
    * Equivalent to the Configure_IO_Port procedure of Ada
    */

   __po_hi_driver_xc4v_fpga_configure_ioports ();
   __po_hi_driver_xc4v_drv_addr = __po_hi_driver_xc4v_bar0;
   return 1;
}

unsigned __po_hi_driver_xc4v_fpga_read_register (unsigned offset) 
{
   unsigned int xc4v_pci_address;
   unsigned int* data;
   __PO_HI_DRIVER_XC4V_INIT_FPGA

   xc4v_pci_address = (unsigned int)__po_hi_driver_xc4v_drv_addr;
   data = (unsigned int*)(xc4v_pci_address + offset);

   return *data;
}

void __po_hi_driver_xc4v_fpga_write_register (unsigned offset, unsigned value) {
   __PO_HI_DRIVER_XC4V_INIT_FPGA
   unsigned int xc4v_pci_address;
   unsigned int* data;

   xc4v_pci_address = (unsigned int)__po_hi_driver_xc4v_drv_addr;
   data = (unsigned int*)(xc4v_pci_address + offset);

   *data = value;
}

#endif /* __PO_HI_NEED_DRIVER_XC4V_FPGA */
