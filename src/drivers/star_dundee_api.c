/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://www.openaadl.org
 *
 * Copyright (C) 2018-2019 ESA & ISAE, 2019-2020 OpenAADL
 */

#include<po_hi_debug.h>
#include "star_dundee_api.h"

/******************************************************************************/
size_t dundee_sending
(void* message,
 int message_size,
 STAR_CHANNEL_ID selectedChannel) {

  size_t size = message_size;
  if (size ==0){
    __PO_HI_DEBUG_CRITICAL
      ("The length of the to-be-sent packet is 0, aborting.\n");
    return 0;
  }

  /* Create a message_size packet to be transmitted, terminated with an EOP */
  STAR_STREAM_ITEM *pHeader, *pTxStreamItem, *packet[2];
  STAR_SPACEWIRE_ADDRESS *pAddress = NULL;

  unsigned char header[4] = { '1', '3', '0', '0'};
  
  pHeader = STAR_createDataChunk
    (header, 4, 1, STAR_EOP_TYPE_NONE);
  if (!pTxStreamItem){
    __PO_HI_DEBUG_CRITICAL
      ("Couldn't create the stream item to be transmitted.\n");
    return 0;
  }
  
  pTxStreamItem = STAR_createDataChunk
    (message, message_size, 0, STAR_EOP_TYPE_EOP);
  if (!pTxStreamItem){
    __PO_HI_DEBUG_CRITICAL
      ("Couldn't create the stream item to be transmitted.\n");
    return 0;
  }

  packet[0] = pHeader;
  packet[1] = pTxStreamItem;
  
  /* Create a transfer operation to transmit the packet */

  STAR_TRANSFER_OPERATION *pTxTransOp;
  pTxTransOp = STAR_createTxOperation(&packet, 2);
  if (!pTxTransOp){
    __PO_HI_DEBUG_CRITICAL("Couldn't create the transmit operation.\n");
    STAR_destroyStreamItem(pHeader);
    STAR_destroyStreamItem(pTxStreamItem);
    return 0;
  }

  /* Start transmitting the packet */
  (void)STAR_submitTransferOperation(selectedChannel, pTxTransOp);

  /* Wait indefinitely on the transmit completing */
  STAR_TRANSFER_STATUS status;
  status = STAR_waitOnTransferOperationCompletion(pTxTransOp, -1);
  if (status != STAR_TRANSFER_STATUS_COMPLETE){
    __PO_HI_DEBUG_CRITICAL("Could not transmit packet, error of %d.", status);
    return 0;
  }

  /* Dispose of the transmit operation */
  (void)STAR_disposeTransferOperation(pTxTransOp);

  /* Destroy the transmit packet */
  STAR_destroyStreamItem(pHeader);
  STAR_destroyStreamItem(pTxStreamItem);

  /* Return the size of the data */
  return size;
}

/******************************************************************************/
size_t dundee_receiving(void* message, STAR_CHANNEL_ID selectedChannel){

  size_t size = 0;
  unsigned int receiveBufferLength;
  unsigned char *pReceiveBuffer;

  /* Create a transfer operation for receiving one packet */
  STAR_TRANSFER_OPERATION *pRxTransOp;
  pRxTransOp = STAR_createRxOperation(1, STAR_RECEIVE_PACKETS);
  if (!pRxTransOp){
    __PO_HI_DEBUG_CRITICAL("Couldn't create receive operation, exiting.\n");
    return 0;
  }

  /* Start receiving a packet */
  STAR_submitTransferOperation(selectedChannel, pRxTransOp);

  /* Wait indefinitely on a packet being received */
  STAR_TRANSFER_STATUS status;
  status = STAR_waitOnTransferOperationCompletion(pRxTransOp, -1);
  if (status != STAR_TRANSFER_STATUS_COMPLETE){
    __PO_HI_DEBUG_CRITICAL("Could not receive packet, error of %d.\n", status);
    STAR_disposeTransferOperation(pRxTransOp);
    return 0;
  }

  /* Get the stream item received */
  STAR_STREAM_ITEM *pRxStreamItem;
  pRxStreamItem = STAR_getTransferItem(pRxTransOp, 0);
  if (!pRxStreamItem){
    __PO_HI_DEBUG_CRITICAL("Unable to get the stream item received. \n");
    STAR_disposeTransferOperation(pRxTransOp);
    return 0;
  }

  /* Get the bytes of the packet received */
  pReceiveBuffer = STAR_getPacketData((STAR_SPACEWIRE_PACKET *)pRxStreamItem->item,&receiveBufferLength);
  if (!pReceiveBuffer){
    __PO_HI_DEBUG_CRITICAL("Unable to get the contents of the packet.\n");
    STAR_disposeTransferOperation(pRxTransOp);
    return 0;
  }

  /* Here the length is both header and data */

  memcpy (message, pReceiveBuffer + 4, receiveBufferLength - 4);

  /* Display the bytes in the packet */
  __PO_HI_DEBUG_CRITICAL("Received packet contents:\n");
  __PO_HI_DEBUG_CRITICAL(" \n");
  size = receiveBufferLength;

  if (size ==0){
    __PO_HI_DEBUG_CRITICAL("The length of the received packet is 0. \n");
  }

  /* Destroy the buffer containing the received packet, once the
     message is copied. */
  STAR_destroyPacketData(pReceiveBuffer);

  /* Dispose of the receive operation */;
  STAR_disposeTransferOperation(pRxTransOp);
  return size;
}
