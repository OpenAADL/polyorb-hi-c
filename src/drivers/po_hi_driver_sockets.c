/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2010, European Space Agency
 * Copyright (C) 2007-2008, GET-Telecom Paris.
 */

#include <deployment.h>
#include <marshallers.h>

#if (defined (__PO_HI_NEED_DRIVER_SOCKETS) || defined (__PO_HI_NEED_DRIVER_QEMU_NE2000_SOCKETS))

#include <po_hi_config.h>
#include <po_hi_task.h>
#include <po_hi_transport.h>
#include <po_hi_debug.h>
#include <po_hi_types.h>
#include <po_hi_messages.h>
#include <po_hi_returns.h>
#include <po_hi_main.h>
#include <po_hi_task.h>
#include <drivers/po_hi_driver_sockets.h>

#ifdef __PO_HI_USE_GIOP
#include <po_hi_giop.h>
#endif

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
 * This file (po_hi_sockets.c) provides function to handle
 * communication between nodes in PolyORB-HI-C.  We don't use a
 * protocol to send data. For each data sent, we send before the
 * entity number provided by the generated file deployment.h, then, we
 * send the message.  Each entity has a fixed size
 * (sizeof(__po_hi_entity_t)), and each message has a max fixed size
 * (see the __PO_HI_MESSAGES_MAX_SIZE macro).
 */

/* The following declarations avoid conflicts
 * with current generated code.
 */

#ifndef __PO_HI_NB_NODES
#define __PO_HI_NB_NODES 1
#endif

/*
 * We have two arrays of sockets. The first array (nodes) is used to
 * send data to other nodes. A special socket if nodes[mynode] : this
 * socket is used to listen others processes.  The second array
 * (rnodes), is used to store all socket that are created by the
 * listen socket. This array is used only by the receiver_task
 */

__po_hi_inetnode_t nodes[__PO_HI_NB_NODES];
__po_hi_inetnode_t rnodes[__PO_HI_NB_NODES];

int __po_hi_driver_sockets_send (__po_hi_entity_t from, 
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

#ifdef __PO_HI_USE_GIOP
   size_to_write = msg->length;
#else
   size_to_write = __PO_HI_MESSAGES_MAX_SIZE;
#endif

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

void* __po_hi_sockets_receiver_task (void)
{
   socklen_t          socklen = sizeof (struct sockaddr);
   /* See ACCEPT (2) for details on initial value of socklen */

   __po_hi_uint32_t   len;
   int                sock;
   int                max_socket;
   fd_set             selector;
   __po_hi_msg_t      msg;
#ifdef __PO_HI_USE_GIOP
   __po_hi_msg_t      decoded_msg;
   __po_hi_uint32_t   has_more;
#endif
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
         if (sock == -1)
         {
            __DEBUGMSG ("accept() failed, return=%d\n", sock);
         }

         if (read (sock, &node_init, sizeof (__po_hi_node_t)) != sizeof (__po_hi_node_t))
         {
            __DEBUGMSG ("Cannot read node-id for socket %d\n", sock);
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

#ifdef __PO_HI_USE_GIOP
            /* Decoding GIOP request is implemented as a two-step automata
             * 
             * First step is to decode the header,
             * Second step is to decode the payload
             */

            __DEBUGMSG ("Using GIOP as protocol stack\n");
            __DEBUGMSG (" -> Step 1 decode header\n");
            len = read (rnodes[node].socket, &(msg.content), sizeof (__po_hi_giop_msg_hdr_t));
            msg.length = len;

            has_more = 0; 

            if (__po_hi_giop_decode_msg (&msg, &decoded_msg, &has_more) == __PO_HI_SUCCESS )
            {
#ifdef __PO_HI_DEBUG
               __DEBUGMSG ("Message was decoded, has_more=%d\n", has_more);
#endif
               __DEBUGMSG (" -> Step 2 decode message\n");
               len = recv (rnodes[node].socket, &(msg.content), has_more, MSG_WAITALL);
               /* Here, we wait for the _full_ message to come */
               msg.length = len;

               if (__po_hi_giop_decode_msg (&msg, &decoded_msg, &has_more) == __PO_HI_SUCCESS )
               {
                  /* Put the data in the message queue */      
                  __po_hi_unmarshall_request (&received_request, &decoded_msg);
                  __po_hi_main_deliver (&received_request);
               }
               else
               {
                  break;
               }
            }
            else
            {
               break;
            }

#else
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
#endif
            __po_hi_msg_reallocate(&msg);        /* re-initialize the message */
         }
      }
   }  
   return NULL;
}


extern __po_hi_device_id my_id;
void* __po_hi_sockets_poller (void)
{
   __DEBUGMSG ("Poller launched\n");
   socklen_t          socklen = sizeof (struct sockaddr);
   /* See ACCEPT (2) for details on initial value of socklen */

   __po_hi_uint32_t   len;
   int                sock;
   int                max_socket;
   fd_set             selector;
   struct sockaddr_in sa;
   __po_hi_node_t     dev;
   __po_hi_node_t     dev_init;
   __po_hi_request_t  received_request;
   __po_hi_msg_t      msg;

   max_socket = 0; /* Used to compute the max socket number, useful for listen() call */

   /*
    * We initialize each node socket with -1 value.  This value means
    * that the socket is not active.
    */
   for (dev = 0 ; dev < __PO_HI_NB_DEVICES ; dev++)
   {
      rnodes[dev].socket = -1;
   }

   /*
    * Create a socket for each node that will communicate with us.
    */
   for (dev = 0; dev < __PO_HI_NB_DEVICES ; dev++)
   {
      if (dev != my_id)
      {
         sock = accept (nodes[my_id].socket, (struct sockaddr*) &sa, &socklen);

         if (read (sock, &dev_init, sizeof (__po_hi_device_id)) != sizeof (__po_hi_device_id))
         {
            __DEBUGMSG ("[DRIVER SOCKETS] Cannot read device-id for device %d, socket=%d\n", dev, sock);
            continue;
         }
         __DEBUGMSG ("[DRIVER SOCKETS] read device-id %d from socket=%d\n", dev_init, sock);
         rnodes[dev].socket = sock;
         if (sock > max_socket )
         {
            max_socket = sock;
         }	  
      }
   }
   __DEBUGMSG ("[DRIVER SOCKETS] Poller initialization finished\n");
   __po_hi_wait_initialization ();

   /*
    * Then, listen and receive data on the socket, identify the node
    * which send the data and put it in its message queue
    */
   while (1)
   {
      FD_ZERO( &selector );
      for (dev = 0; dev < __PO_HI_NB_DEVICES ; dev++)
      {
         if ( (dev != my_id ) && ( rnodes[dev].socket != -1 ) )
         {
            FD_SET( rnodes[dev].socket , &selector );
         }
      }

      if (select (max_socket + 1, &selector, NULL, NULL, NULL) == -1 )
      {
#ifdef __PO_HI_DEBUG
         __DEBUGMSG ("[DRIVER SOCKETS] Error on select for node %d\n", mynode);
#endif 
      }
#ifdef __PO_HI_DEBUG
      __DEBUGMSG ("[DRIVER SOCKETS] Receive message\n");
#endif

      for (dev = 0; dev < __PO_HI_NB_DEVICES ; dev++)
      {
         if ( (rnodes[dev].socket != -1 ) && FD_ISSET(rnodes[dev].socket, &selector))
         {
            __DEBUGMSG ("[DRIVER SOCKETS] Receive message from dev %d\n", dev);
            memset (msg.content, '\0', __PO_HI_MESSAGES_MAX_SIZE);
            len = recv (rnodes[dev].socket, msg.content, __PO_HI_MESSAGES_MAX_SIZE, MSG_WAITALL);
            __DEBUGMSG ("[DRIVER SOCKETS] Message received len=%d\n",len);

            if (len == 0)
            {
               rnodes[dev].socket = -1;
               continue;
            }

            __po_hi_unmarshall_request (&received_request, &msg);

            __po_hi_main_deliver (&received_request);
         }
      }
   }  
   return NULL;
}



#endif

