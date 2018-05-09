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

#define DEVS_MAX 32 /** Maximum number of devices supported */

#define PKT_SIZE __PO_HI_MESSAGES_MAX_SIZE + 42 /** Size of the packets exchanged */

/** Structure representing a GRPSW device */
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

/** AUXILIARY INITIALIZATION FUNCTION :
 * Initializing the devices.
 *
 * Application thread
 *  TDRX. SpaceWire DMA RX task. Handles reception of SpaceWire
 *        packets on all SpaceWire devices.
 *  TDTX. SpaceWire DMA RX task. Handles transmission of SpaceWire
 *        packets on all SpaceWire devices.
 *  Then Semaphores : dma_sync_rx and dma_sync tx.
 *  Then the reception and transmission tasks are started.
 */
void grspw_api_init(void);

/** Function that close and clean the idx GRSPW-device.
 * All dma channels need to be closed before closing the device.
 * Error messages are returned whether the dma isn't closed correctly
 * Or if it's the case for the device.
 * Used in test_app.
 */
void dev_cleanup(int idx);

/** SpaceWire Routing table entry */
struct route_entry {
  unsigned char dstadr[16];
  /* 0 terminates array */
};

/** Function following a sending process:
 * A packet is taking at the head of the tx_buf_list.
 * Its data content is extracted from the "message" parameter.
 * Its header is initialized according to the content of the p_route parameter.
 * Its length is initalized thanks to the message_size parameter.
 * The pkt is then added to the tx_list (to be sent).
 * The dma_sem semaphore is used so that the tasks don't overlap.
 * The dma_sync_tx is used so that the task isn't periodic but is triggered
 * only when something is about to be sent.
 * The function is called in the test_app Task, used with the sending command (x command).
*/
size_t grspw_sending
  (int device,
   struct route_entry * p_route,
   void *message, int message_size);

/** Function following a receiving process:
 * A packet is taking at the head of the tx_buf_list (of the specified device).
 * Its data content is extracted from the "message" parameter.
 * Its header is initialized according to the content of the p_route parameter.
 * Its length is initalized thanks to the message_size parameter.
 * The pkt is then added to the tx_list (to be sent).
 * The dma_sem semaphore is used so that the tasks don't overlap.
 * The dma_sync_rx is used so that the task isn't periodic but is triggered
 * only when something is about to be received.
 * The function is called in the test_app Task, used qith the receiving command (r command).
*/
size_t grspw_receiving(int device,void *message);


#endif /*__GRSPW_API_H__ */
