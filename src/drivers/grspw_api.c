/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://www.openaadl.org
 *
 * Copyright (C) 2018-2019 ESA & ISAE, 2019-2020 OpenAADL
 */

/* This driver relies on the GRSPW2 Packet library proposed in RTEMS
 * 4.11 and 5. It supports a more sophisticated way to handle packets
 * in memory, coupled with DMA. See RCC manuals for more details.
 *
 * Note: this implementation relies on elements from the grspw-test
 * sample programs provided in RCC 1.3rc4 by Cobham Gaisler.
 */

#include "grspw_api.h"

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h> // exit
#include <string.h> // memset

#include <rtems.h>

/* SpaceWire parameters */
#define SPW_PROT_ID 3

/* Configuration of the driver */

/* Total number of packets */
#define PKT_NBR 16

/* Packets allowed to transmission */
#define PKT_NBR_LIMIT (PKT_NBR / 2)

/* Number of supplementary bytes to avoid truncated packets */
#define EXTRA_BYTES 8

/* The header is coded on 4 bytes (documentation) */
#define HEADER_SIZE 4

/** Macros used with the GRSPW devices */
#define DEV(device) ((struct grspw_dev *)(device))

/* DECLARATION OF STRUCTURES AND RTEMS ELEMENTS */

/* Declaration of the transmission/reception task used in test_app */
rtems_task dma_task_rx(rtems_task_argument unused);
rtems_task dma_task_tx(rtems_task_argument unused);

/* Tasks ID corresponding*/
rtems_id tid_dma_rx, tid_dma_tx;

/* Driver internal data structures */

/**
 * \struct spwpkt.
 * \brief Structure used as a bridge in the grspw_pkt data and header implementation.
 */
struct spwpkt {
  struct grspw_pkt p;

  /* 32 bytes of data (- 4byte data-header) and 8 extra bytes to avoid
     truncated bad packets */
  int data[PKT_SIZE + EXTRA_BYTES];

  /* up to 16byte header (path address) before but 4 bytes is enough */
  int hdr[16];
};

/** Array listing all packet buffers used by application for each device */
struct spwpkt pkts[DEVS_MAX][PKT_NBR];

/* Macros used to make a task Wait */
#define BLOCK 2
#define timeout 32

/** Integer that will represent the maximum number of devices */
int nospw;

/* FORWARD DECLARATION OF ELEMENTS USED IN grspw_api_init FUNCTION */

/* Declaration of semaphores responsible of the synchronization between tasks */
rtems_id dma_sem;
rtems_id dma_sync_tx;
rtems_id dma_sync_rx;
/* Used in the Routing process */
extern int router_setup_custom(void);

/* Other functions */
void init_pkts(void);
int dev_init(int idx);

void grspw_api_init(void){
  int i;
  extern struct router_hw_info router_hw;

  /* INITIALIZING ROUTER PORTS, DEVICES AND DMA */
  /* Initialize two GRSPW AMBA ports */
  printf("Setting up SpaceWire router\n");
  if (router_setup_custom()) {
    printf("Failed router initialization, assuming that it does not exists\n");
  }
  else {
    /* on-chip router found */
    if (router_hw.nports_amba < 2) {
      printf("Error. Router with less than 2 AMBA ports not supported\n");
      exit(0);
    }
  }
  /* Obtain the number of GRSPW devices registered to the driver.*/
  nospw = grspw_dev_count();
  printf("dev_count = %d\n", grspw_dev_count());
  printf("nospw = %d\n",nospw);
  if (nospw < 1) {
    /* no device found */
    printf("Found no SpaceWire cores, aborting\n");
    exit(0);
  }

  if (nospw > DEVS_MAX) {
    /* too many devices, restriction awaited */
    printf("Limiting to %d SpaceWire devices\n", DEVS_MAX);
    nospw = DEVS_MAX;
  }

  memset(devs, 0, sizeof(devs));
  /* Initialize all GRSPW devices registered to the driver*/
  for (i=0; i<nospw; i++) {
    if (dev_init(i)) {
      printf("Failed to initialize GRSPW%d\n", i);
      exit(0);
    }
    fflush(NULL);
  }
  /* Initialize GRSPW (Device and DMA) */
  init_pkts();
  printf("\n\nStarting SpW DMA channels\n");
  for (i = 0; i < nospw; i++) {
    printf("Starting GRSPW%d: ", i);
    fflush(NULL);
    if (grspw_start(DEV(&devs[i]))) {
      printf("Failed to initialize GRSPW%d\n", i);
      exit(0);
    }
    printf("DMA Started Successfully\n");
  }
  fflush(NULL);

  /* Run SpaceWire Test application */
  rtems_task_create(
                    rtems_build_name( 'T', 'D', 'R', 'X' ),
                    10, RTEMS_MINIMUM_STACK_SIZE * 10, RTEMS_DEFAULT_MODES,
                    RTEMS_FLOATING_POINT, &tid_dma_rx);
  rtems_task_create(
                    rtems_build_name( 'T', 'D', 'T', 'X' ),
                    10, RTEMS_MINIMUM_STACK_SIZE * 10, RTEMS_DEFAULT_MODES,
                    RTEMS_FLOATING_POINT, &tid_dma_tx);

  /* Device Semaphore responsible of the synchronisation, created with
     count = 1 */
  if (rtems_semaphore_create(rtems_build_name('S', 'E', 'M', '0'), 1,
                             RTEMS_FIFO | RTEMS_SIMPLE_BINARY_SEMAPHORE | \
                             RTEMS_NO_INHERIT_PRIORITY | RTEMS_LOCAL |	\
                             RTEMS_NO_PRIORITY_CEILING, 1, &dma_sem) != RTEMS_SUCCESSFUL){
    printf("Failed creating dma_sem Semaphore\n");
    exit(0);
  }
  /* Device Semaphore responsible of the transmission task, created with count = 0 */
  if (rtems_semaphore_create(rtems_build_name('S', 'E', 'M', '1'), 0,
                             RTEMS_FIFO | RTEMS_SIMPLE_BINARY_SEMAPHORE | \
                             RTEMS_NO_INHERIT_PRIORITY | RTEMS_LOCAL |	\
                             RTEMS_NO_PRIORITY_CEILING, 0, &dma_sync_tx) != RTEMS_SUCCESSFUL){
    printf("Failed creating dma_sync_tx Semaphore\n");
    exit(0);
  }
  /* Device Semaphore responsible of the reception task, created with count = 0 */
  if (rtems_semaphore_create(rtems_build_name('S', 'E', 'M', '2'), 0,
                             RTEMS_FIFO | RTEMS_SIMPLE_BINARY_SEMAPHORE | \
                             RTEMS_NO_INHERIT_PRIORITY | RTEMS_LOCAL |	\
                             RTEMS_NO_PRIORITY_CEILING, 0, &dma_sync_rx) != RTEMS_SUCCESSFUL){
    printf("Failed creating dma_sync_rx Semaphore\n");
    exit(0);
  }

  rtems_task_start(tid_dma_rx, dma_task_rx, 0);
  rtems_task_start(tid_dma_tx, dma_task_tx, 0);

}
/**
 * \brief Function that initialize all packets of the application, splitting them in RX and TX packets.
 * 
 * Using the spwpkt structure as a bridge to fill the different packets. \n
 * The initialized TX packets are put in the tx_buf_list to be sent (in test_app). \n
 * The initialized RX packets are put in the rx_list so that the "prepare" function (in dma_rx) 
 * put them in the rx_ready list, to provide empty packets for Reception. \n
 */
void init_pkts(void){
  struct spwpkt *pkt;
  int i, j;
  memset(&pkts[0][0], 0, sizeof(pkts));

  for (i = 0; i < DEVS_MAX; i++) {
    grspw_list_clr(&devs[i].rx_list);
    grspw_list_clr(&devs[i].tx_list);
    grspw_list_clr(&devs[i].tx_buf_list);
    devs[i].rx_list_cnt = 0;
    devs[i].tx_list_cnt = 0;
    devs[i].tx_buf_list_cnt = 0;
    devs[i].rx_buf_list_cnt = 0;

    for (j = 0, pkt = &pkts[i][0]; j < PKT_NBR; j++, pkt = &pkts[i][j]){
      pkt->p.pkt_id = (i << 8) + j; /* unused */
      /* pkt->p.data has also as a value the adress of pkt.data, pkt being a spwpkt */
      pkt->p.data = &pkt->data[0];
      pkt->p.hdr = &pkt->hdr[0];
      /* (PKT_NBR - PKT_NBR_LIMIT) Packets allowed to reception */
      if (j < PKT_NBR - PKT_NBR_LIMIT) {
        /* RX buffer */
        /* Add to device RX list */
        grspw_list_append(&devs[i].rx_list, &pkt->p);
        devs[i].rx_list_cnt++;
      }
      /* (PKT_NBR_LIMIT) Packets allowed to transmission */
      else {
        /* TX buffer */
        pkt->p.dlen = PKT_SIZE;

        /* Initialize at 0 on the space destined to the data */
        memset(pkt->p.data + HEADER_SIZE, 0, PKT_SIZE - HEADER_SIZE);

        /* Adding the packet to device tx_buf_list */
        grspw_list_append(&devs[i].tx_buf_list, &pkt->p);
        devs[i].tx_buf_list_cnt++;
      }
    }
  }
}

/* Function playing with the timecode */
void app_tc_isr(void *data, int tc);
void app_tc_isr(void *data, int tc){
        struct grspw_device *dev = data;
        printf("GRSPW%d: TC-ISR received 0x%02x\n", dev->index, tc);
}

/** Variable used to configure a GRSPW-device cfg attribute */
struct grspw_config dev_def_cfg =
{
  .adrcfg =
  {
    .promiscuous = 1, /* Detect all packets */
    .def_addr = 32, /* updated bu dev_init() */
    .def_mask = 0,
    .dma_nacfg =
    {
      /* Since only one DMA Channel is used, only
       * the default Address|Mask is used.
       */
      {
        .node_en = 0,
        .node_addr = 0,
        .node_mask = 0,
      },
      {
        .node_en = 0,
        .node_addr = 0,
        .node_mask = 0,
      },
      {
        .node_en = 0,
        .node_addr = 0,
        .node_mask = 0,
      },
      {
        .node_en = 0,
        .node_addr = 0,
        .node_mask = 0,
      },
    },
  },
  .rmap_cfg = 0,		/* Disable RMAP */
  .rmap_dstkey = 0,	/* No RMAP DESTKEY needed when disabled */
  .tc_cfg = TCOPTS_EN_TX|TCOPTS_EN_RX,/* Enable TimeCode */
  .tc_isr_callback = app_tc_isr,/* TimeCode ISR */
  .tc_isr_arg = NULL,	/* No TimeCode ISR Argument */
  .enable_chan_mask = 1,	/* Enable only the first DMA Channel */
  .chan =
  {
    {
      .flags = DMAFLAG_NO_SPILL,
      .rxmaxlen = PKT_SIZE+4,
      .rx_irq_en_cnt = 0, /* Disable RX IRQ generation */
      .tx_irq_en_cnt = 0, /* Disable TX IRQ generation */
    },
    /* The other 3 DMA Channels are unused */
  },
};

/**
 * \brief Function fully initializing the idx Device.
 * 
 * It especially returns an error message if only one port is available or
 * if the device can't open correctly. \n
 * It also resets all packets lists. \
 * \param idx identifier of the device.
 * \return 0 if successful.
 * \return -1 if there is an error.
 */
int dev_init(int idx){
        struct grspw_device *dev = &devs[idx];
        int i, ctrl, clkdiv, tc;

        printf(" Initializing SpaceWire device %d\n", idx);

        memset(dev, 0, sizeof(struct grspw_device));

        dev->index = idx;
        /* pointer relative to the good opening of the device */
        dev->dh = grspw_open(idx);
        if (dev->dh == NULL) {
                printf("Failed to open GRSPW device %d\n", idx);
                return -1;
        }
        grspw_hw_support(dev->dh, &dev->hwsup);

#ifdef PRINT_GRSPW_RESET_CFG
        grspw_config_read(DEV(dev), &dev->cfg);
        printf("\n\n---- DEFAULT CONFIGURATION FROM DRIVER/HARDWARE ----\n");
        grspw_cfg_print(&dev->hwsup, &dev->cfg);
#endif

        dev->cfg = dev_def_cfg;
        dev->cfg.adrcfg.def_addr = 32 + idx;
        dev->cfg.tc_isr_arg = dev;
        tc = TCOPTS_EN_TX | TCOPTS_EN_RX | TCOPTS_EN_RXIRQ;
        grspw_tc_ctrl(dev->dh, &tc);

        if (grspw_cfg_set(DEV(dev), &dev->cfg)) {
          grspw_close(dev->dh);
          return -1;
        }

#ifdef PRINT_GRSPW_RESET_CFG
        printf("\n\n---- APPLICATION CONFIGURATION ----\n");
        grspw_cfg_print(&dev->hwsup, &dev->cfg);
        printf("\n\n");
#endif

        /* This will result in an error if only one port available */
        if (dev->hwsup.nports < 2) {
          int port = 1;
          if ( grspw_port_ctrl(dev->dh, &port) == 0 ) {
            printf("Succeeded to select port1, however only one PORT on dev %d!\n", dev->index);
            return -1;
          }
        }

        /* Try to bring link up at fastest clockdiv but do not touch
         * start-up clockdivisor */
        clkdiv = -1;
        grspw_link_ctrl(dev->dh, NULL, NULL, &clkdiv);
        ctrl = LINKOPTS_ENABLE | LINKOPTS_AUTOSTART | LINKOPTS_START;
        clkdiv &= 0xff00;
        grspw_link_ctrl(dev->dh, &ctrl, NULL, &clkdiv);

#if 0
        if ( (dev->hwsup.hw_version >> 16) == GAISLER_SPW2_DMA ){
          printf(" NOTE: running on SPW-ROUTER DMA SpaceWire link (no link-state available)\n");
        }
        else{
          printf(" After Link Start: %d\n", (int)grspw_link_state(dev->dh));
        }
#endif

        dev->run = 0;

        grspw_stats_clr(dev->dh);

        for (i=0; i<dev->hwsup.ndma_chans; i++) {
          if (dev->dma[i]){
            grspw_dma_stats_clr(dev->dma[i]);
          }
        }
        grspw_list_clr(&dev->rx_list);
        grspw_list_clr(&dev->tx_list);
        grspw_list_clr(&dev->tx_buf_list);
        dev->rx_list_cnt = dev->tx_list_cnt = dev->tx_buf_list_cnt = dev->rx_buf_list_cnt= 0;

        return 0;
}

/**
 * \brief Function that close all dma channels for a specified device idx.
 *
 * If the dma channel is active,
 * it is closed and the NULL value is imput in the dma array. \n
 * If the closing is correctly done, returns 0. \n
 * 
 * \param idx identifier of the device.
 * \return 0 if a successful closing is done.
 * \return the result of dma_close if there is an error.
 */
int dev_dma_close_all(int idx){
  struct grspw_device *dev = &devs[idx];
  int i, rc;
  /* Going through all dma channels, close if opened before*/
  for (i=0; i<dev->hwsup.ndma_chans; i++) {
    if (dev->dma[i]) {
      rc = grspw_dma_close(dev->dma[i]);
      if (rc){
        return rc;
      }
      dev->dma[i] = NULL;
    }
  }
  return 0;
}

void dev_cleanup(int idx){
  struct grspw_device *dev = &devs[idx];
  if (dev->dh == NULL)
    return;

  /* Stop all DMA activity first */
  grspw_stop(DEV(dev));

  /* Wait for other tasks to be thrown out from driver */
  rtems_task_wake_after(4);

  /* Close all DMA channels */
  if (dev_dma_close_all(idx)) {
    printf("FAILED to close GRSPW%d DMA\n", idx);
  }

  /* Close the selected device, which needs all DMA channel closed*/
  if (grspw_close(dev->dh)) {
    printf("FAILED to close GRSPW%d\n", idx);
  }
  dev->dh = NULL;
}

/* FORWARD DECLARATION OF PKT_INIT_HDR FUNCTION */
void pkt_init_hdr(struct grspw_pkt *pkt, struct route_entry *route, int idx);

size_t grspw_sending
(int device,
 struct route_entry * p_route,
 void *message, int message_size){

  rtems_semaphore_obtain(dma_sem, RTEMS_WAIT, RTEMS_NO_TIMEOUT);
  size_t message_size_sent = message_size;
  struct grspw_pkt *pkt;
  /* Get a TX packet buffer */
  /* Taking a packet at the head */
  pkt = devs[device].tx_buf_list.head;
  if (pkt != NULL) {
    /* The new head is the following pkt, pkt->next */
    devs[device].tx_buf_list.head = pkt->next;
    devs[device].tx_buf_list_cnt--;
    if (pkt->next == NULL){
      /* It was the last TX packet */
      devs[device].tx_buf_list.tail = NULL;
    }
    /* Header Init */
    pkt_init_hdr(pkt,p_route, device);

    /* Message Initialisation, assuming 1 byte = 1 char */
    if (message_size <= PKT_SIZE - HEADER_SIZE){
      memcpy (pkt->data + HEADER_SIZE, message, message_size);
      /* The header is included in the dlen on HEADER_SIZE bytes */
      pkt->dlen  = message_size + HEADER_SIZE;
      char *data = ((char *)pkt->data);
      printf("data[1]=%d", data[1]);
      printf("\n");
    }
    else{
      printf("Message too long not initialized ");
    }
    printf(" X%d: scheduling packet on GRSPW%d\n",device, device);
    /* Send packet by adding it to the tx_list */
    grspw_list_append(&devs[device].tx_list, pkt);
    devs[device].tx_list_cnt++;
    rtems_semaphore_release(dma_sync_tx);
  }
  else {
    /* Tx_buf_list is empty */
    printf("No free transmit buffers available\n");
    /* the dma_sync_tx is not released */
    //continue;
  }
  rtems_semaphore_release(dma_sem);
  return message_size_sent;
}

size_t grspw_receiving(int device,void *message){
  rtems_semaphore_obtain(dma_sync_rx, RTEMS_WAIT, RTEMS_NO_TIMEOUT);
  rtems_semaphore_obtain(dma_sem, RTEMS_WAIT, RTEMS_NO_TIMEOUT);
  size_t message_size_received = 0;

  struct grspw_pkt *pkt;
  /* Get a RX packet buffer from the HEAD */

  pkt = devs[device].rx_buf_list.head;
  if (pkt != NULL) {
    /* The new head is the following pkt, pkt->next */
    devs[device].rx_buf_list.head = pkt->next;
    devs[device].rx_buf_list_cnt--;
    if (pkt->next == NULL){
      /* It was the last RX packet */
      devs[device].rx_buf_list.tail = NULL;
    }
    /* Assuming 1 byte = 1 char */
    /* The header is included in the dlen on HEADER_SIZE bytes */
    message_size_received = pkt->dlen - HEADER_SIZE;
    if (message_size_received <= PKT_SIZE - HEADER_SIZE){
      memcpy (message,pkt->data + HEADER_SIZE, message_size_received);
    }
    else{
      printf("Message too long not received ");
    }
    /* Reschedule packet by adding it to the rx_list */
    grspw_list_append(&devs[device].rx_list, pkt);
    devs[device].rx_list_cnt++;
  }
  else{
    /* rx_buf_list is empty */
    printf(" No free received buffers available, size 0\n");
    //continue;
  }
  rtems_semaphore_release(dma_sem);
  return message_size_received;
}

/**
 * \struct pkt_hdr.
 * \brief SpaceWire packet payload (data) content layout.
 * 
 * Structure used to fill the first bytes of the GRSPW-pkt Data.
 * It is particularly used in the pkt_init_hdr function.
 */
struct pkt_hdr {
  unsigned char addr;
  unsigned char protid;
  /* Port index of source */
  unsigned char port_src;

  /* Resv2 : Zero for now */
  unsigned char resv2;

  /* Data array used to implement the GRSPW-pkt data */
  //unsigned int data[(PKT_SIZE-4)/4];
  unsigned int data[PKT_SIZE + EXTRA_BYTES];
};

/**
 * \brief Function that initialize the packet header of the pkt, and the Data payload header.
 * 
 * The pkt is leaving the idx Device. \n
 * The pkt_hdr structure is used to modify the first bytes of the GRSPW-pkt Data (destination, device..). \n
 * The hdr array is used to implement in the GRSPW-pkt Hdr the different Adresses,
 * IF there are non-first Destination Addresses. \n
 * 
 * \param pkt the pkt targeted. 
 * \param route the routing table. 
 * \param idx identifier of the device. 
 */
void pkt_init_hdr(struct grspw_pkt *pkt, struct route_entry *route, int idx){
  int i;
  struct pkt_hdr *pkt_hdr = (struct pkt_hdr *)pkt->data;
  unsigned char *hdr = pkt->hdr;

  /* In path addressing we put non-first Destination Addresses in
   * header. If there is only one destination, (i=0)
   * route->dstadr[0] is always non-zero (written in test_app) */
  i = 0;
  while ( route->dstadr[i+1] != 0 ){
    hdr[i] = route->dstadr[i];
    i++;
  }
  printf("hdr[0] = %d, \n", hdr[0]);
  /* */
  pkt->hlen = i;

  /* Put last address/Destination device in pkt_hdr->addr */
  pkt_hdr->addr = route->dstadr[i];
  pkt_hdr->protid = SPW_PROT_ID;
  printf("pkt_hdr->protid = %d, \n", pkt_hdr->protid);

  /* Sending device */
  pkt_hdr->port_src = idx;
  pkt_hdr->resv2 = 0;
}

/* FORWARD DECLARATION OF FUNCTIONS USED IN TRANSMISSION AND RECEPTION */
int dma_process_rx(struct grspw_device *dev);
int dma_process_tx(struct grspw_device *dev);

/**
 * \brief Task handling the reception.
 * 
 * The dma_sem semaphore is used so that the tasks don't overlap. \n
 * The dma_sync_rx is used so that the task isn't periodic but is triggered
 * only when something is about to be received. \n
 * It checks all active devices and calls the dma_process_rx function. \n
 */
rtems_task dma_task_rx(rtems_task_argument unused){
  int i;
  struct grspw_device *dev;
  printf("Started DMA-rx control task\n");

  while (true) {
    rtems_semaphore_obtain(dma_sem, RTEMS_WAIT, RTEMS_NO_TIMEOUT);

    for (i = 0; i < nospw; i++) {
      dev = &devs[i];
      if (dev->dh == NULL)
        continue;
      dma_process_rx(dev);
    }
    rtems_semaphore_release(dma_sem);
  }

  printf(" DMA task shutdown\n");
  rtems_task_delete(RTEMS_SELF);
}
/**
 * \brief Task handling the transmission.
 * 
 * The dma_sem semaphore is used so that the tasks don't overlap. \n
 * The dma_sync_tx is used so that the task isn't periodic but is triggered
 * only when something is about to be sent. \n
 * It checks all active devices and calls the dma_process_tx function. \n
 */
rtems_task dma_task_tx(rtems_task_argument unused){
  int i;
  struct grspw_device *dev;
  printf("Started DMA-tx control task\n");

  while (true) {
    rtems_semaphore_obtain(dma_sync_tx, RTEMS_WAIT, RTEMS_NO_TIMEOUT);
    rtems_semaphore_obtain(dma_sem, RTEMS_WAIT, RTEMS_NO_TIMEOUT);
    for (i = 0; i < nospw; i++) {
      dev = &devs[i];
      if (dev->dh == NULL)
        continue;
      dma_process_tx(dev);
    }
    rtems_semaphore_release(dma_sem);
    //rtems_task_wake_after(20);
  }

  printf(" DMA task shutdown\n");
  rtems_task_delete(RTEMS_SELF);
}

/**
 * \brief Function called in the task dma_process_rx, used in the receiving process.
 *
 * The list lst is cleared to receive the received packets. \n
 * A rx_wait is done, then the packets are received from the RX_RECV
 *   list (cf documentation) with rx_recv. \n
 * The obtained message is printed, then the packets are moved
 *   (append) to the rx_buf_list. (They will be moved from the
 *   rx_buf_list to the rx_list in the grspw_receiving function.) \n
 * Then the reception is prepared with rx_prepare with putting Empty
 *   packet from rx_list to RX-READY (cf documentation). \n
 * The rx_list is then cleared. \n
 * \return 0 if there is no conflict.
 */
int dma_process_rx(struct grspw_device *dev){

  int cnt, rc;
  struct grspw_list lst;
  struct grspw_pkt *pkt;
  unsigned char *c;

  int rx_ready, rx_sched, rx_recv, rx_hwcnt;
  int tx_send, tx_sched, tx_sent, tx_hwcnt;

  /* Counting the packets */
  grspw_dma_rx_count(dev->dma[0], &rx_ready, &rx_sched, &rx_recv, &rx_hwcnt);
  grspw_dma_tx_count(dev->dma[0], &tx_send, &tx_sched, &tx_sent, &tx_hwcnt);

  if (rx_hwcnt >= 127) {
    printf(" DMA DRVQ RX_READY: %d\n", rx_ready);
    printf(" DMA DRVQ RX_SCHED: %d\n", rx_sched);
    printf(" DMA DRVQ RX_RECV: %d\n", rx_recv);
    printf(" DMA DRVQ RX_HWCNT: %d\n", rx_hwcnt);
  }
  /* RX PART */
  /* Try to receive packets on receiver interface */
  grspw_list_clr(&lst);

  /* Initialize cnt to receive as many packets as possible */
  cnt = -1;

  /* The wait function is used to prioritize the tasks */
  rc = grspw_dma_rx_wait(dev->dma[0], BLOCK, 0, BLOCK, timeout);

  /* Received Packets go to lst */
  rc = grspw_dma_rx_recv(dev->dma[0], 0, &lst, &cnt);

  /* Checking the reception */
  if (rc != 0) {
    printf("rx_recv failed %d\n", rc);
    return -1;
  }

  if (cnt > 0) {
    printf("GRSPW%d: Received %d packets", dev->index, cnt);

    for (pkt = lst.head; pkt; pkt = pkt->next) {
      if ((pkt->flags & RXPKT_FLAG_RX) == 0) {
        printf(" PKT not received.. buf ret\n");
        continue;
      } else if (pkt->flags &
                 (RXPKT_FLAG_EEOP | RXPKT_FLAG_TRUNK))
        {
          printf(" PKT RX errors:");
          if (pkt->flags & RXPKT_FLAG_TRUNK)
            printf(" truncated");
          if (pkt->flags & RXPKT_FLAG_EEOP)
            printf(" EEP");
          printf(" (0x%x)", pkt->flags);
        } else
        printf(" \n");

      /* Printing what has been received */
      /* The informations are in the data array */
      c = (unsigned char *)pkt->data;
      printf(" hlen of length %d bytes,", pkt->hlen);
      printf(" dlen of length %d bytes,", pkt->dlen);
      printf("PKT of length %d bytes", pkt->dlen + pkt->hlen);
      printf("\n");

      /* The header is included in the dlen on HEADER_SIZE bytes */
      for (int i=0;i<pkt->dlen;i++){
        c[i] = ((unsigned char *)pkt->data)[i];
        printf(" %c", c[i]);
      }
      printf("\n");

      /* Adding that to work on the header/data */
      for (int i=0;i<pkt->dlen;i++){
        c[i] = ((unsigned char *)pkt->data)[i];
        printf(" %d", c[i]);
      }
      printf("\n");
    }

    /* Reuse packet by moving packets from lst to rx_buf_list (put in
     * rx_list in test_app)
     */

    grspw_list_append_list(&dev->rx_buf_list, &lst);
    dev->rx_buf_list_cnt += cnt;
  }

  /* Release the semaphore blocking task in grspw_receiving() if
   * something is found in the buffer
   */
  pkt = (&dev->rx_buf_list)->head;
  if (pkt != NULL) {
    rtems_semaphore_release(dma_sync_rx);
  }

  /* Prepare receiver with packet buffers */
  if (dev->rx_list_cnt > 0) {
    /* Put Empty packets from rx_list in RX-READY */
    rc = grspw_dma_rx_prepare
      (dev->dma[0], 0, &dev->rx_list, dev->rx_list_cnt);

    if (rc != 0) {
      /* Pkts not successfully added */
      printf("rx_prep failed %d\n", rc);
      return -1;
    }

    grspw_list_clr(&dev->rx_list);
    dev->rx_list_cnt = 0;
  }
  return 0;
}

/**
 * \brief Function called in the task dma_process_tx, used in the sending process.
 *
 * The list lst is cleared to receive the sent packets. \n
 * The packets are received from the TX_SENT list (cf documentation) with tx_reclaim. \n
 * The packets are moved (append) to the tx_buf_list. \n
 * (They will be moved from the tx_buf_list to the tx_list in the grspw_sending function.) \n
 * The obtained message is printed. \n
 * Then the sending is prepared with tx_send with putting the packet from tx_list to TX-SEND (cf documentation). \n
 * The tx_list is then cleared. \n
 * \return 0 if there is no conflict.
 */

/** Function called in the task dma_process_tx, used in the sending process :
 * The list lst is cleared to receive the sent packets.
 * The packets are received from the TX_SENT list (cf documentation) with tx_reclaim.
 * The packets are moved (append) to the tx_buf_list.
 * (They will be moved from the tx_buf_list to the tx_list in the grspw_sending function.)
 * The obtained message is printed.
 * Then the sending is prepared with tx_send with putting the packet from tx_list to TX-SEND (cf documentation).
 * The tx_list is then cleared.
*/

int dma_process_tx(struct grspw_device *dev){
  int cnt, rc, i;
  struct grspw_list lst;
  struct grspw_pkt *pkt;
  unsigned char *c;

  int rx_ready, rx_sched, rx_recv, rx_hwcnt;
  int tx_send, tx_sched, tx_sent, tx_hwcnt;

  grspw_dma_rx_count(dev->dma[0], &rx_ready, &rx_sched, &rx_recv, &rx_hwcnt);
  grspw_dma_tx_count(dev->dma[0], &tx_send, &tx_sched, &tx_sent, &tx_hwcnt);
  if (rx_hwcnt >= 127) {
    printf(" DMA DRVQ TX_SEND: %d\n", tx_send);
    printf(" DMA DRVQ TX_SCHED: %d\n", tx_sched);
    printf(" DMA DRVQ TX_SENT: %d\n", tx_sent);
    printf(" DMA DRVQ TX_HWCNT: %d\n", tx_hwcnt);
  }

  /* TX PART */
  /* Reclaim already transmitted buffers */
  /* Initialize cnt to receive as many packets as possible */
  cnt = -1;
  grspw_list_clr(&lst);

  /* Moving already-sent packets from the SENT queue to lst */
  rc = grspw_dma_tx_reclaim(dev->dma[0], 0, &lst, &cnt);
  if (rc != 0) {
    printf("tx_reclaim failed %d\n", rc);
    exit(0);
  }

  if (cnt > 0) {
    /* Clear transmission flags */
    pkt = lst.head;
    while (pkt) {
      if ((pkt->flags & TXPKT_FLAG_TX) == 0)
        printf(" One Packet TX failed\n");
      else if (pkt->flags & TXPKT_FLAG_LINKERR)
        printf(" One Packet with TX errors\n");
      pkt = pkt->next;
    }
    /* Moving the retrieved packets from lst to tx_buf_list */
    grspw_list_append_list(&dev->tx_buf_list, &lst);
    dev->tx_buf_list_cnt += cnt;
  }

  if (dev->tx_list_cnt > 0) {
    printf("GRSPW%d: Sending %d packets\n", dev->index,dev->tx_list_cnt);
    for (pkt = dev->tx_list.head; pkt; pkt = pkt->next) {
      printf(" hlen of length %d bytes,", pkt->hlen);
      printf(" dlen of length %d bytes,", pkt->dlen);
      printf(" PKT of length %d bytes", pkt->hlen+pkt->dlen);
      printf("\n");
      /* Printing what is going to be sent */
      c = (unsigned char *)pkt->data;
      for (i=0;i< pkt->dlen;i++){
        c[i] = ((unsigned char *)pkt->data)[i];
        printf(" %c", c[i]);
      }
      printf("\n");
      /*Adding that to work on the header/data */
      for (i=0;i< pkt->dlen;i++){
        c[i] = ((unsigned char *)pkt->data)[i];
        printf(" %d", c[i]);
      }
      printf("\n");
    }
    /* Moving to-be-sent packets from the tx_list to the send queue */
    rc = grspw_dma_tx_send(dev->dma[0], 0, &dev->tx_list,
                           dev->tx_list_cnt);
    if (rc != 0) {
      printf("tx_send failed %d\n", rc);
      exit(0);
                        }
    dev->tx_list_cnt = 0;
    grspw_list_clr(&dev->tx_list);
  }
  return 0;
}
