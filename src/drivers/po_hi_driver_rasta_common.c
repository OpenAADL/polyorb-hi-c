/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2010-2016 ESA & ISAE.
 */

#include <deployment.h>
/* Generated code header */

#if ((defined __PO_HI_NEED_DRIVER_SPACEWIRE_RASTA) || \
     (defined __PO_HI_NEED_DRIVER_SERIAL_RASTA))

#include <rtems/bspIo.h>
#include <pci.h>
#include <rasta.h>
#include <ambapp.h>
#include <grspw_rasta.h>

#include <pci.h>
#include <rasta.h>
#include <apbuart_rasta.h>
/* Rasta includes from GAISLER drivers */

#include <po_hi_debug.h>
/* PolyORB-HI-C includes */

#define DBG printk

/* If RASTA_SRAM is defined SRAM will be used, else SDRAM */
/*#define RASTA_SRAM 1*/

#define RASTA_IRQ  5

/* Offset from 0x80000000 (dual bus version) */
#define AHB1_IOAREA_BASE_ADDR 0x80100000
#define APB2_OFFSET    0x200000
#define IRQ_OFFSET     0x200500
#define GRHCAN_OFFSET  0x201000
#define BRM_OFFSET     0x100000
#define SPW_OFFSET     0xa00
#define UART_OFFSET    0x200200
#define GPIO0_OFF      0x200600
#define GPIO1_OFF      0x200700

#ifndef GAISLER_GPIO
#define GAISLER_GPIO         0x01a
#endif

int __po_hi_c_driver_rasta_common_is_init = 0;

#ifdef RTEMS48
int apbuart_rasta_register(amba_confarea_type *bus);
static amba_confarea_type abus;
extern LEON3_IrqCtrl_Regs_Map *irq;
extern LEON_Register_Map      *regs;

amba_confarea_type* __po_hi_driver_rasta_common_get_bus ()
{
   return &abus;
}
#elif RTEMS411
extern int apbuart_rasta_register(struct ambapp_bus *bus);
static struct ambapp_bus  abus;
/* Why do we have LEON3 specifics here ???
extern LEON3_IrqCtrl_Regs_Map *irq;
extern LEON_Register_Map      *regs;
*/
struct ambapp_bus * __po_hi_driver_rasta_common_get_bus ()
{
   return &abus;
}
#else
#error "o<"
#endif

void *uart0_int_arg, *uart1_int_arg;
void *spw0_int_arg, *spw1_int_arg, *spw2_int_arg;
void *grcan_int_arg;
void *brm_int_arg;

extern void (*uart0_int_handler)(int irq, void *arg);
extern void (*uart1_int_handler)(int irq, void *arg);
extern void (*spw0_int_handler)(int irq, void *arg);
extern void (*spw1_int_handler)(int irq, void *arg);
extern void (*spw2_int_handler)(int irq, void *arg);
extern void (*grcan_int_handler)(int irq, void *arg);
extern void (*brm_int_handler)(int irq, void *arg);



unsigned int __po_hi_driver_rasta_bar0, __po_hi_driver_rasta_bar1;

/*

void __po_hi_rasta_interrrupt_register(void *handler, int irqno, void *arg)
{
  DBG("RASTA: Registering irq %d\n",irqno);
  if ( irqno == UART0_IRQNO ){
    DBG("RASTA: Registering uart0 handler: 0x%x, arg: 0x%x\n",handler,arg);
    uart0_int_handler = handler;
    uart0_int_arg = arg;
    
    irq->iclear = UART0_IRQ;
    irq->mask[0] |= UART0_IRQ;
  }
  
  if ( irqno == UART1_IRQNO ){
    DBG("RASTA: Registering uart1 handler: 0x%x, arg: 0x%x\n",handler,arg);
    uart1_int_handler = handler;
    uart1_int_arg = arg;
    
    irq->iclear = UART1_IRQ;
    irq->mask[0] |= UART1_IRQ;
  }
  
  if ( irqno == SPW0_IRQNO ){
    DBG("RASTA: Registering spw0 handler: 0x%x, arg: 0x%x\n",handler,arg);
    spw0_int_handler = handler;
    spw0_int_arg = arg;
    
    irq->iclear = SPW0_IRQ;
    irq->mask[0] |= SPW0_IRQ;
  }

  if ( irqno == SPW1_IRQNO ){
    DBG("RASTA: Registering spw1 handler: 0x%x, arg: 0x%x\n",handler,arg);
    spw1_int_handler = handler;
    spw1_int_arg = arg;
    
    irq->iclear = SPW1_IRQ;
    irq->mask[0] |= SPW1_IRQ;
  }
  
  if ( irqno == SPW2_IRQNO ){
    DBG("RASTA: Registering spw2 handler: 0x%x, arg: 0x%x\n",handler,arg);
    spw2_int_handler = handler;
    spw2_int_arg = arg;
    
    irq->iclear = SPW2_IRQ;
    irq->mask[0] |= SPW2_IRQ;
  }
  
  if ( irqno == GRCAN_IRQNO ){
    DBG("RASTA: Registering GRCAN handler: 0x%x, arg: 0x%x\n",handler,arg);
    grcan_int_handler = handler;
    grcan_int_arg = arg;
    
    irq->iclear = GRCAN_IRQ;
    irq->mask[0] |= GRCAN_IRQ;
  }
  
  if ( irqno == BRM_IRQNO ){
    DBG("RASTA: Registering BRM handler: 0x%x, arg: 0x%x\n",handler,arg);
    brm_int_handler = handler;
    brm_int_arg = arg;
    
    irq->iclear = BRM_IRQ;
    irq->mask[0] |= BRM_IRQ;
  } 
}


static rtems_isr __po_hi_rasta_interrupt_handler (rtems_vector_number v)
{
    unsigned int status;
 
    status = irq->ipend;

    if ( (status & GRCAN_IRQ) && grcan_int_handler ) {
      grcan_int_handler(GRCAN_IRQNO,grcan_int_arg);
    }
    
    if (status & SPW_IRQ) {
      if ( (status & SPW0_IRQ) && spw0_int_handler ){
        spw0_int_handler(SPW0_IRQNO,spw0_int_arg);
      }

      if ( (status & SPW1_IRQ) && spw1_int_handler ){
        spw1_int_handler(SPW1_IRQNO,spw1_int_arg);
      }
      
      if ( (status & SPW2_IRQ) && spw2_int_handler ){
        spw2_int_handler(SPW2_IRQNO,spw2_int_arg);
      }
    }
    if ((status & BRM_IRQ) && brm_int_handler ){ 
        brm_int_handler(BRM_IRQNO,brm_int_arg);
    }
    if ( (status & UART0_IRQ) && uart0_int_handler ) {
      uart0_int_handler(UART0_IRQNO,uart0_int_arg);
    }
    if ( (status & UART1_IRQ) && uart1_int_handler) {
      uart1_int_handler(UART1_IRQNO,uart1_int_arg);
    }
    
    DBG("RASTA-IRQ: 0x%x\n",status);
    irq->iclear = status;
 
}


int __po_hi_rasta_register(void) 
{
       unsigned int bar0, bar1, data;

    unsigned int *page0 = NULL;
    unsigned int *apb_base = NULL;
    int found=0;
    

    DBG("Searching for RASTA board ...");
    
    if (BSP_pciFindDevice(0x1AC8, 0x0010, 0, &bus, &dev, &fun) == 0) {
      found = 1;
    }
    
    if ( (!found) && (BSP_pciFindDevice(0x16E3, 0x0210, 0, &bus, &dev, &fun) == 0) ) {
      found = 1;
    }
    
    if ( !found )
      return -1;
    
    DBG(" found it (dev/fun: %d/%d).\n", dev, fun);

    pci_read_config_dword(bus, dev, fun, 0x10, &bar0);
    pci_read_config_dword(bus, dev, fun, 0x14, &bar1);

    page0 = (unsigned int *)(bar0 + 0x400000); 
    *page0 = 0x80000000;

    apb_base = (unsigned int *)(bar0+APB2_OFFSET);

#ifdef RASTA_SRAM
    apb_base[0] = 0x000002ff;
    apb_base[1] = 0x00001260;
    apb_base[2] = 0x000e8000;
#else 
    apb_base[0] = 0x000002ff;
    apb_base[1] = 0x82206000;
    apb_base[2] = 0x000e8000;
#endif
    irq = (LEON3_IrqCtrl_Regs_Map *) (bar0+IRQ_OFFSET); 
    irq->iclear = 0xffff;
    irq->ilevel = 0;
    irq->mask[0] = 0xffff & ~(UART0_IRQ|UART1_IRQ|SPW0_IRQ|SPW1_IRQ|SPW2_IRQ|GRCAN_IRQ|BRM_IRQ);

    regs->PIO_Direction &= ~(1<<7);
    regs->PIO_Interrupt |= (0x87<<8);

    apb_base[0x100] |= 0x40000000;
    apb_base[0x104] =  0x40000000;

    
    pci_read_config_dword(bus, dev, fun, 0x4, &data);
    pci_write_config_dword(bus, dev, fun, 0x4, data|0x40);
     
    pci_master_enable(bus, dev, fun);

    set_vector(__po_hi_rasta_interrupt_handler, RASTA_IRQ+0x10, 1);

    amba_maps[0].size = 0x10000000;
    amba_maps[0].cpu_adr = bar0;
    amba_maps[0].remote_amba_adr = 0x80000000;

    amba_maps[1].size = 0x10000000;
    amba_maps[1].cpu_adr = bar1;
    amba_maps[1].remote_amba_adr = 0x40000000;

    amba_maps[2].size=0;
    amba_maps[2].cpu_adr = 0;
    amba_maps[2].remote_amba_adr = 0;
        
    memset(&abus,0,sizeof(abus));
        
    amba_scan(&abus,bar0+(AHB1_IOAREA_BASE_ADDR&~0xf0000000),&amba_maps[0]);
        
    printk("Registering RASTA BRM driver\n\r");

    b1553brm_rasta_int_reg=__po_hi_rasta_interrrupt_register;
          if ( b1553brm_rasta_register(&abus,2,0,3,bar1,0x40000000) ){
      printk("Failed to register BRM RASTA driver\n");
      return -1;
    }
        
    grspw_rasta_int_reg=__po_hi_rasta_interrrupt_register;
    if ( grspw_rasta_register(&abus,bar1) ){
      printk("Failed to register RASTA GRSPW driver\n\r");
      return -1;
    }

    apbuart_rasta_int_reg=__po_hi_rasta_interrrupt_register;
    if ( apbuart_rasta_register(&abus) ){
      printk("Failed to register RASTA APBUART driver\n\r");
      return -1;
    }

    if ( rasta_get_gpio(&abus,0,&gpio0,NULL) ){
      printk("Failed to get address for RASTA GPIO0\n\r");
      return -1;
    }
        
    if ( rasta_get_gpio(&abus,1,&gpio1,NULL) ){
      printk("Failed to get address for RASTA GPIO1\n\r");
      return -1;
    }
    
    return 0;
}
*/


void __po_hi_c_driver_rasta_common_init ()
{
   if (__po_hi_c_driver_rasta_common_is_init == 1)
   {
      __PO_HI_DEBUG_DEBUG ("[RASTA COMMON] RASTA already initialized, pass init\n");
      return;
   }

   __PO_HI_DEBUG_DEBUG ("[RASTA COMMON] Init\n");
   init_pci();
   __PO_HI_DEBUG_DEBUG ("[RASTA COMMON] Initializing RASTA ...");
  /*
  if  (__po_hi_rasta_register() ){
    __PO_HI_DEBUG_DEBUG (" ERROR !\n");
    return;
  }
  */

  if  (rasta_register() ){
    __PO_HI_DEBUG_DEBUG(" ERROR !\n");
    return;
  }

    __PO_HI_DEBUG_DEBUG (" OK !\n");

   __po_hi_c_driver_rasta_common_is_init = 1;
}

#endif
