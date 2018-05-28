#ifndef __GRSPW_API_H__
#define __GRSPW_API_H__

/* This unit provides a high-level set of help functions for the new
 * GRSPW packet driver. See RCC 1.3 Chapter 18 documentation for
 * details.
 *
 * Note: this implementation relies on elements from the grspw-test
 * sample program provided in RCC 1.3rc4 by Cobham Gaisler, and the
 * grspw_pkt_lib auxiliary library.
 */

#include <drvmgr/drvmgr_confdefs.h>
#include <bsp/grspw_pkt.h>
#include <bsp/grspw_router.h>

#include <stddef.h>

#include "grspw_pkt_lib.h"

#include <po_hi_messages.h>

#define DEVS_MAX 32 /* Maximum number of devices supported */

#define PKT_SIZE __PO_HI_MESSAGES_MAX_SIZE + 42 /* Size of the packets exchanged */

/**
 * \struct grspw_device.
 * \brief Structure representing a GRPSW device.
 */
struct grspw_device {
  /* GRSPW Device layout - must be the same as 'struct grspw_dev' */
  void *dh;
  /* Array of DMA Channels */
  void *dma[4];
  int index;
  /* Structure to describe the GRSPW hardware capabilities */
  struct grspw_hw_sup hwsup;
  /* Test structures */
  struct grspw_config cfg;
  int run;
  /* RX and TX lists of packet buffers */
  struct grspw_list rx_list, tx_list, tx_buf_list,rx_buf_list;
  int rx_list_cnt, tx_list_cnt, tx_buf_list_cnt, rx_buf_list_cnt;
};

/** Array listing all GRSPW devices */
static struct grspw_device devs[DEVS_MAX];

/**
 * \brief Auxiliary Initialization function to initialize the devices.
 * 
 * Application thread : \n
 * TDRX. SpaceWire DMA RX task. Handles reception of SpaceWire
 *        packets on all SpaceWire devices. \n
 * TDTX. SpaceWire DMA RX task. Handles transmission of SpaceWire
 *        packets on all SpaceWire devices. \n
 * Then Semaphores : dma_sync_rx and dma_sync tx. \n
 * Then the reception and transmission tasks are started. \n
 */
void grspw_api_init(void);

/**
 * \brief Function that close and clean a GRSPW-device.
 * 
 * All dma channels need to be closed before closing the device. \n
 * Error messages are returned whether the dma isn't closed correctly,
 * Or if it's the case for the device. \n
 * \param idx identifier of the device.
 */
void dev_cleanup(int idx);

/**
 * \struct route_entry;
 * \brief SpaceWire Routing table entry.
 */
struct route_entry {
  unsigned char dstadr[16];
  /* 0 terminates array */
};

/**
 * \brief Function following a sending process.
 *
 * A packet is taken at the head of the tx_buf_list. \n
 * Its data content is extracted from the "message" parameter. \n
 * Its header is initialized according to the content of the p_route parameter. \n
 * Its length is initalized thanks to the message_size parameter. \n
 * The pkt is then added to the tx_list (to be sent). \n
 * The dma_sem semaphore is used so that the tasks don't overlap. \n
 * The dma_sync_tx is used so that the task isn't periodic but is triggered 
 * only when something is about to be sent. \n
 * The function is called in the main task and used with the sending command (x). \n
 * 
 * \param device the identifier of the device.
 * \param p_route a pointer toward the spacewire routing table.
 * \param message which will contain the message.
 * \param message_size the size of the message sent.
 * \return size the size of the message sent.
 */
size_t grspw_sending
  (int device,
   struct route_entry * p_route,
   void *message, int message_size);

/**
 * \brief Function following a receiving process.
 *
 * A packet is taken at the head of the tx_buf_list (of the specified device). \n
 * Its data content is extracted from the "message" parameter. \n
 * Its header is initialized according to the content of the p_route parameter. \n
 * Its length is initalized thanks to the message_size parameter. \n 
 * The pkt is then added to the tx_list (to be sent). \n
 * The dma_sem semaphore is used so that the tasks don't overlap. \n
 * The dma_sync_rx is used so that the task isn't periodic but is triggered
 * only when something is about to be received. \n
 * The function is called in the main Task, used qith the receiving command (r). \n
 * 
 * \param device the identifier of the device.
 * \param message which will contain the message.
 * \return size the size of the message received.
 */
size_t grspw_receiving(int device,void *message);


#endif /*__GRSPW_API_H__ */
