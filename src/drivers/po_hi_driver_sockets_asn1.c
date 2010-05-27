/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2010, European Space Agency
 */

#include <deployment.h>
#include <marshallers.h>

#ifdef __PO_HI_NEED_DRIVER_SOCKETS_ASN1

#include <po_hi_config.h>
#include <po_hi_task.h>
#include <po_hi_transport.h>
#include <drivers/po_hi_driver_sockets.h>
#include <po_hi_debug.h>
#include <po_hi_types.h>
#include <po_hi_messages.h>
#include <po_hi_returns.h>
#include <po_hi_main.h>
#include <po_hi_task.h>

#include <activity.h>

#include <signal.h>
#include <string.h>
#include <unistd.h>
#include <netdb.h>
#include <sys/types.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <sys/time.h>

/*
 * This file contains an implementation of a socket driver
 * that send and receive data through POSIX sockets but encode
 * data with the ASN1 protocol.
 */

/* The following declarations avoid conflicts
 * with current generated code.
 */

#ifndef __PO_HI_NB_NODES
#define __PO_HI_NB_NODES 1
#endif

typedef struct
{
   int socket;
} __po_hi_inetnode_t;

/*
 * We have two arrays of sockets. The first array (nodes) is used to
 * send data to other nodes. A special socket if nodes[mynode] : this
 * socket is used to listen others processes.  The second array
 * (rnodes), is used to store all socket that are created by the
 * listen socket. This array is used only by the receiver_task
 */

__po_hi_inetnode_t nodes[__PO_HI_NB_NODES];
__po_hi_inetnode_t rnodes[__PO_HI_NB_NODES];

int __po_hi_driver_sockets_asn1_send (__po_hi_entity_t from, 
                                      __po_hi_entity_t to, 
                                      __po_hi_msg_t* msg)
{
   __po_hi_node_t  node;
   int             len;
   int             size_to_write;
   int             optval = 0;
   socklen_t       optlen = 0;

   node = __po_hi_transport_get_node_from_entity (to);

   if (nodes[node].socket == -1 )
   {
#ifdef __PO_HI_DEBUG
      __DEBUGMSG (" [... failure ...]\n");
#endif
      return __PO_HI_ERROR_TRANSPORT_SEND;		
   }

   /*
    * After sending the entity identifier, we send the message which
    * contains the request.
    */

   size_to_write = __PO_HI_MESSAGES_MAX_SIZE;

   if (getsockopt (nodes[node].socket, SOL_SOCKET, SO_ERROR, &optval, &optlen) == -1)
   {
      __DEBUGMSG (" [error getsockopt() in file %s, line%d ]\n", __FILE__, __LINE__);
      close (nodes[node].socket);
      nodes[node].socket = -1;
      return __PO_HI_ERROR_TRANSPORT_SEND;		
   }

   if (optval != 0)
   {
      __DEBUGMSG (" [error getsockopt() return code in file %s, line%d ]\n", __FILE__, __LINE__);
      close (nodes[node].socket);
      nodes[node].socket = -1;
      return __PO_HI_ERROR_TRANSPORT_SEND;		
   }

   /* Ignore SIGPIPE to be able to recover from errors instead of crashing the node */

   if (signal (SIGPIPE, SIG_IGN) == SIG_ERR)
   {
      __DEBUGMSG (" [error signal() return code in file %s, line%d ]\n", __FILE__, __LINE__);
      close (nodes[node].socket);
      nodes[node].socket = -1;
      return __PO_HI_ERROR_TRANSPORT_SEND;		
   }

#ifdef __PO_HI_DEBUG
   __po_hi_messages_debug (msg);
#endif

   len = write (nodes[node].socket, &(msg->content), size_to_write);

   if (len != size_to_write)
   {
      __DEBUGMSG (" [error write() length in file %s, line%d ]\n", __FILE__, __LINE__);
      close (nodes[node].socket);
      nodes[node].socket = -1;
      return __PO_HI_ERROR_TRANSPORT_SEND;		
   }

   __DEBUGMSG (" [SUCCESS]\n");

   return __PO_HI_SUCCESS;
}


void* __po_hi_sockets_asn1_poller (void)
{
   socklen_t          socklen = sizeof (struct sockaddr);
   /* See ACCEPT (2) for details on initial value of socklen */

   __po_hi_uint32_t   len;
   int                sock;
   int                max_socket;
   fd_set             selector;
   __po_hi_msg_t      msg;
   __po_hi_node_t     node;
   __po_hi_node_t     node_init;
   __po_hi_request_t  received_request;
   struct sockaddr_in sa;

   max_socket = 0; /* Used to compute the max socket number, useful for listen() call */

   /*
    * We initialize each node socket with -1 value.  This value means
    * that the socket is not active.
    */
   for (node = 0 ; node < __PO_HI_NB_NODES ; node++)
   {
      rnodes[node].socket = -1;
   }

   /*
    * Create a socket for each node that will communicate with us.
    */
   for (node = 0; node < __PO_HI_NB_NODES ; node++)
   {
      if (node != mynode )
      {
         sock = accept (nodes[mynode].socket, (struct sockaddr*) &sa, &socklen);

         if (read (sock, &node_init, sizeof (__po_hi_node_t)) != sizeof (__po_hi_node_t))
         {
#ifdef __PO_HI_DEBUG
            __DEBUGMSG ("Cannot read node-id for socket %d\n", sock);
#endif
            continue;
         }
         rnodes[node].socket = sock;
         if (sock > max_socket )
         {
            max_socket = sock;
         }	  
      }
   }
#ifdef __PO_HI_DEBUG
   __DEBUGMSG ("Receiver initialization finished\n");
#endif
   __po_hi_wait_initialization ();

   /*
    * Then, listen and receive data on the socket, identify the node
    * which send the data and put it in its message queue
    */
   while (1)
   {
      FD_ZERO( &selector );
      for (node = 0; node < __PO_HI_NB_NODES ; node++)
      {
         if ( (node != mynode ) && ( rnodes[node].socket != -1 ) )
         {
            FD_SET( rnodes[node].socket , &selector );
         }
      }

      if (select (max_socket + 1, &selector, NULL, NULL, NULL) == -1 )
      {
#ifdef __PO_HI_DEBUG
         __DEBUGMSG ("Error on select for node %d\n", mynode);
#endif 
      }
#ifdef __PO_HI_DEBUG
      __DEBUGMSG ("Receive message\n");
#endif

      for (node = 0; node < __PO_HI_NB_NODES ; node++)
      {
         if ( (rnodes[node].socket != -1 ) && FD_ISSET(rnodes[node].socket, &selector))
         {
#ifdef __PO_HI_DEBUG
            __DEBUGMSG ("Receive message from node %d\n", node);
#endif

            __DEBUGMSG ("Using raw protocol stack\n");
            len = recv (rnodes[node].socket, &(msg.content), __PO_HI_MESSAGES_MAX_SIZE, MSG_WAITALL);
            msg.length = len;
            if (len != __PO_HI_MESSAGES_MAX_SIZE )
            {
               __DEBUGMSG ("ERROR, %u %d", (unsigned int) len, __PO_HI_MESSAGES_MAX_SIZE);
               close (rnodes[node].socket);
               rnodes[node].socket = -1;
               continue;
            }
            __DEBUGMSG ("Message delivered");

            __po_hi_unmarshall_request (&received_request, &msg);

            __po_hi_main_deliver (&received_request);
            __po_hi_msg_reallocate(&msg);        /* re-initialize the message */
         }
      }
   }  
   return NULL;
}

#endif /* __PO_HI_NEED_DRIVER_SOCKETS_ASN1 */

