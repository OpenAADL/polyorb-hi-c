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

#include <rtems/bspIo.h>
#include <pci.h>
#include <rasta.h>
#include <ambapp.h>

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


void rasta_interrrupt_register(void *handler, int irqno, void *arg);

int apbuart_rasta_register(amba_confarea_type *bus);

int __po_hi_c_driver_rasta_common_is_init = 0;

static int bus, dev, fun;
static amba_confarea_type abus;
static struct amba_mmap amba_maps[3];
extern LEON3_IrqCtrl_Regs_Map *irq;
extern LEON_Register_Map      *regs;

amba_confarea_type* __po_hi_driver_rasta_common_get_bus ()
{
   return &abus;
}


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

static rtems_isr __po_hi_rasta_interrupt_handler (rtems_vector_number v)
{
    unsigned int status;
 
    status = irq->ipend;
    DBG("Interrupt triggered\n");

    if ( (status & GRCAN_IRQ) && grcan_int_handler ) {

    DBG("CAN triggered\n");
      grcan_int_handler(GRCAN_IRQNO,grcan_int_arg);
    }
    
    if (status & SPW_IRQ) {
      if ( (status & SPW0_IRQ) && spw0_int_handler ){
    DBG("SPW0 triggered\n");
        spw0_int_handler(SPW0_IRQNO,spw0_int_arg);
      }

      if ( (status & SPW1_IRQ) && spw1_int_handler ){
    DBG("SPW1 triggered\n");
        spw1_int_handler(SPW1_IRQNO,spw1_int_arg);
      }
      
      if ( (status & SPW2_IRQ) && spw2_int_handler ){
    DBG("SPW2 triggered\n");
        spw2_int_handler(SPW2_IRQNO,spw2_int_arg);
      }
    }
    if ((status & BRM_IRQ) && brm_int_handler ){ 
    DBG("BRM triggered\n");
        brm_int_handler(BRM_IRQNO,brm_int_arg);
    }
    if ( (status & UART0_IRQ) && uart0_int_handler ) {
    DBG("UART0 triggered\n");
      uart0_int_handler(UART0_IRQNO,uart0_int_arg);
    }
    if ( (status & UART1_IRQ) && uart1_int_handler) {
    DBG("UART1 triggered\n");
      uart1_int_handler(UART1_IRQNO,uart1_int_arg);
    }
    irq->iclear = status;
}

void __po_hi_rasta_interrrupt_register(void *handler, int irqno, void *arg)
{
  DBG("RASTA: Registering irq %d\n",irqno);
  if ( irqno == UART0_IRQNO ){
    DBG("RASTA: Registering uart0 handler: 0x%x, arg: 0x%x\n",handler,arg);
    uart0_int_handler = handler;
    uart0_int_arg = arg;
    
    /* unmask interrupt source */
    irq->iclear = UART0_IRQ;
    irq->mask[0] |= UART0_IRQ;
  }
  
  if ( irqno == UART1_IRQNO ){
    DBG("RASTA: Registering uart1 handler: 0x%x, arg: 0x%x\n",handler,arg);
    uart1_int_handler = handler;
    uart1_int_arg = arg;
    
    /* unmask interrupt source */
    irq->iclear = UART1_IRQ;
    irq->mask[0] |= UART1_IRQ;
  }
  
  if ( irqno == SPW0_IRQNO ){
    DBG("RASTA: Registering spw0 handler: 0x%x, arg: 0x%x\n",handler,arg);
    spw0_int_handler = handler;
    spw0_int_arg = arg;
    
    /* unmask interrupt source */
    irq->iclear = SPW0_IRQ;
    irq->mask[0] |= SPW0_IRQ;
  }

  if ( irqno == SPW1_IRQNO ){
    DBG("RASTA: Registering spw1 handler: 0x%x, arg: 0x%x\n",handler,arg);
    spw1_int_handler = handler;
    spw1_int_arg = arg;
    
    /* unmask interrupt source */
    irq->iclear = SPW1_IRQ;
    irq->mask[0] |= SPW1_IRQ;
  }
  
  if ( irqno == SPW2_IRQNO ){
    DBG("RASTA: Registering spw2 handler: 0x%x, arg: 0x%x\n",handler,arg);
    spw2_int_handler = handler;
    spw2_int_arg = arg;
    
    /* unmask interrupt source */
    irq->iclear = SPW2_IRQ;
    irq->mask[0] |= SPW2_IRQ;
  }
  
  if ( irqno == GRCAN_IRQNO ){
    DBG("RASTA: Registering GRCAN handler: 0x%x, arg: 0x%x\n",handler,arg);
    grcan_int_handler = handler;
    grcan_int_arg = arg;
    
    /* unmask interrupt source */
    irq->iclear = GRCAN_IRQ;
    irq->mask[0] |= GRCAN_IRQ;
  }
  
  if ( irqno == BRM_IRQNO ){
    DBG("RASTA: Registering BRM handler: 0x%x, arg: 0x%x\n",handler,arg);
    brm_int_handler = handler;
    brm_int_arg = arg;
    
    /* unmask interrupt source */
    irq->iclear = BRM_IRQ;
    irq->mask[0] |= BRM_IRQ;
  } 
}


int __po_hi_rasta_get_gpio(amba_confarea_type *abus, int index, struct gpio_reg **regs, int *irq)
{
  amba_apb_device dev;
  int cores;
  
  if (! abus) 
  {
     __PO_HI_DEBUG_CRITICAL ("[RASTA COMMON] NULL abus\n");
    return -1;
  }
  
  /* Scan PnP info for GPIO port number 'index' */
  cores = amba_find_next_apbslv(abus,VENDOR_GAISLER,GAISLER_GPIO,&dev,index);
  if ( cores < 1 )
  {
    return -1;
  }
  
  if ( regs )
  {
    *regs = (struct gpio_reg *)dev.start;
  }
  
  if ( irq )
  {
    *irq = dev.irq;
  }
  
  return 0;
}




unsigned int __po_hi_driver_rasta_bar0, __po_hi_driver_rasta_bar1;

int __po_hi_rasta_register(void) 
{
   unsigned int data;
    unsigned int *page0 = NULL;
    unsigned int *apb_base = NULL;
    int found=0;
    

    DBG("Searching for RASTA board ...");
    
    /* Search PCI vendor/device id. */
    if (BSP_pciFindDevice(0x1AC8, 0x0010, 0, &bus, &dev, &fun) == 0) {
      found = 1;
    }
    
    /* Search old PCI vendor/device id. */
    if ( (!found) && (BSP_pciFindDevice(0x16E3, 0x0210, 0, &bus, &dev, &fun) == 0) ) {
      found = 1;
    }
    
    /* Did we find a RASTA board? */
    if ( !found )
      return -1;
    
    DBG(" found it (dev/fun: %d/%d).\n", dev, fun);

    pci_read_config_dword(bus, dev, fun, 0x10, &__po_hi_driver_rasta_bar0);
    pci_read_config_dword(bus, dev, fun, 0x14, &__po_hi_driver_rasta_bar1);

    page0 = (unsigned int *)(__po_hi_driver_rasta_bar0 + 0x400000); 
    *page0 = 0x80000000;                  /* Point PAGE0 to start of APB       */

    apb_base = (unsigned int *)(__po_hi_driver_rasta_bar0+APB2_OFFSET);

/*  apb_base[0] = 0x000002ff;
    apb_base[1] = 0x8a205260;
    apb_base[2] = 0x00184000; */

    /* Configure memory controller */
#ifdef RASTA_SRAM
    apb_base[0] = 0x000002ff;
    apb_base[1] = 0x00001260;
    apb_base[2] = 0x000e8000;
#else 
    apb_base[0] = 0x000002ff;
    apb_base[1] = 0x82206000;
    apb_base[2] = 0x000e8000;
#endif
    /* Set up rasta irq controller */
    irq = (LEON3_IrqCtrl_Regs_Map *) (__po_hi_driver_rasta_bar0+IRQ_OFFSET); 
    irq->iclear = 0xffff;
    irq->ilevel = 0;
    irq->mask[0] = 0xffff & ~(UART0_IRQ|UART1_IRQ|SPW0_IRQ|SPW1_IRQ|SPW2_IRQ|GRCAN_IRQ|BRM_IRQ);

    /* Configure AT697 ioport bit 7 to input pci irq */
    regs->PIO_Direction &= ~(1<<7);
    regs->PIO_Interrupt |= (0x87<<8);     /* level sensitive */

    apb_base[0x100] |= 0x40000000;        /* Set GRPCI mmap 0x4 */
    apb_base[0x104] =  0x40000000;        /* 0xA0000000;  Point PAGE1 to RAM */

    /* set parity error response */
    pci_read_config_dword(bus, dev, fun, 0x4, &data);
    pci_write_config_dword(bus, dev, fun, 0x4, data|0x40);

     
    pci_master_enable(bus, dev, fun);

    /* install PCI interrupt vector */
    /*
     */
      
    /* install interrupt vector */

    /*
    set_vector(__po_hi_rasta_interrupt_handler,14+0x10, 1);
    */
    set_vector(__po_hi_rasta_interrupt_handler, RASTA_IRQ+0x10, 1);

    /* Scan AMBA Plug&Play */
	
    /* AMBA MAP bar0 (in CPU) ==> 0x80000000(remote amba address) */
    amba_maps[0].size = 0x10000000;
    amba_maps[0].cpu_adr = __po_hi_driver_rasta_bar0;
    amba_maps[0].remote_amba_adr = 0x80000000;

    /* AMBA MAP bar1 (in CPU) ==> 0x40000000(remote amba address) */
    amba_maps[1].size = 0x10000000;
    amba_maps[1].cpu_adr = __po_hi_driver_rasta_bar1;
    amba_maps[1].remote_amba_adr = 0x40000000;

    /* Mark end of table */
    amba_maps[2].size=0;
    amba_maps[2].cpu_adr = 0;
    amba_maps[2].remote_amba_adr = 0;
        
    memset(&abus,0,sizeof(abus));
        
    /* Start AMBA PnP scan at first AHB bus */
    amba_scan (&abus,__po_hi_driver_rasta_bar0+(AHB1_IOAREA_BASE_ADDR&~0xf0000000),&amba_maps[0]);
    __PO_HI_DEBUG_DEBUG ("abus addr=%x\n", &abus);

    /* Find GPIO0 address */
    if ( __po_hi_rasta_get_gpio(&abus,0,&gpio0,NULL) ){
       printk("Failed to get address for RASTA GPIO0\n\r");
       return -1;
    }


    /* Find GPIO1 address */
    if ( __po_hi_rasta_get_gpio(&abus,1,&gpio1,NULL) ){
      __PO_HI_DEBUG_DEBUG ("Failed to get address for RASTA GPIO1\n\r");
      return -1;
    }
    __PO_HI_DEBUG_DEBUG ("Successful init of the RASTA\n"); 
    /* Successfully registered the RASTA board */
    return 0;
}

void __po_hi_c_driver_rasta_common_init ()
{
   if (__po_hi_c_driver_rasta_common_is_init == 1)
   {
      return;
   }

   __PO_HI_DEBUG_INFO ("[RASTA COMMON] Init\n");
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

