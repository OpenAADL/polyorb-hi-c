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

#if (defined (__PO_HI_NEED_DRIVER_SOCKETS) || \
     defined (__PO_HI_NEED_DRIVER_RTEMS_NE2000_SOCKETS))

#include <po_hi_config.h>
#include <po_hi_task.h>
#include <po_hi_transport.h>
#include <po_hi_debug.h>
#include <po_hi_types.h>
#include <po_hi_messages.h>
#include <po_hi_returns.h>
#include <po_hi_main.h>
#include <po_hi_task.h>
#include <po_hi_gqueue.h>
#include <drivers/po_hi_driver_sockets.h>

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
 * send data to other nodes. A special socket if nodes[__po_hi_mynode] : this
 * socket is used to listen others processes.  The second array
 * (rnodes), is used to store all socket that are created by the
 * listen socket. This array is used only by the receiver_task
 */

__po_hi_inetnode_t nodes[__PO_HI_NB_DEVICES];
__po_hi_inetnode_t rnodes[__PO_HI_NB_DEVICES];

__po_hi_device_id socket_device_id;

int __po_hi_driver_sockets_send (__po_hi_task_id task_id,
                                 __po_hi_port_t port)
{
   int                        len;
   int                        size_to_write;
   int                        optval = 0;
   socklen_t                  optlen = 0;
   __po_hi_device_id          associated_device;
   __po_hi_local_port_t       local_port;
   __po_hi_request_t*         request;
   __po_hi_port_t             destination_port;
   __po_hi_msg_t              msg;
   __po_hi_protocol_t         protocol_id;
   __po_hi_protocol_conf_t*   protocol_conf;

   local_port              = __po_hi_get_local_port_from_global_port (port);
   request                 = __po_hi_gqueue_get_most_recent_value (task_id, local_port);
   destination_port        = __po_hi_gqueue_get_destination (task_id, local_port, 0);
   associated_device       = __po_hi_get_device_from_port (destination_port);
   protocol_id             = __po_hi_transport_get_protocol (port, destination_port);
   protocol_conf           = __po_hi_transport_get_protocol_configuration (protocol_id);

   if (request->port == -1)
   {

#ifdef __PO_HI_DEBUG
      __DEBUGMSG (" [DRIVER SOCKETS] No data to write on port %d\n", port);
#endif
      return __PO_HI_ERROR_TRANSPORT_SEND;
   }

   if (nodes[associated_device].socket == -1 )
   {
#ifdef __PO_HI_DEBUG
      __DEBUGMSG (" [DRIVER SOCKETS] Invalid socket for port-id %d, device-id %d\n", destination_port, associated_device);
#endif
      return __PO_HI_ERROR_TRANSPORT_SEND;		
   }

   /*
    * After sending the entity identifier, we send the message which
    * contains the request.
    */

   size_to_write = __PO_HI_MESSAGES_MAX_SIZE;

   if (getsockopt (nodes[associated_device].socket, SOL_SOCKET, SO_ERROR, &optval, &optlen) == -1)
   {
      __DEBUGMSG (" [error getsockopt() in file %s, line%d ]\n", __FILE__, __LINE__);
      close (nodes[associated_device].socket);
      nodes[associated_device].socket = -1;
      return __PO_HI_ERROR_TRANSPORT_SEND;		
   }

   if (optval != 0)
   {
      __DEBUGMSG (" [error getsockopt() return code in file %s, line%d ]\n", __FILE__, __LINE__);
      close (nodes[associated_device].socket);
      nodes[associated_device].socket = -1;
      return __PO_HI_ERROR_TRANSPORT_SEND;		
   }

   /* Ignore SIGPIPE to be able to recover from errors instead of crashing the node */

   if (signal (SIGPIPE, SIG_IGN) == SIG_ERR)
   {
      __DEBUGMSG (" [error signal() return code in file %s, line%d ]\n", __FILE__, __LINE__);
      close (nodes[associated_device].socket);
      nodes[associated_device].socket = -1;
      return __PO_HI_ERROR_TRANSPORT_SEND;
   }

   switch (protocol_id)
   {
#ifdef __PO_HI_USE_PROTOCOL_MYPROTOCOL_I
      case virtual_bus_myprotocol_i:
      {
         protocol_conf->marshaller(request, &msg);
         break;
      }
#endif
      default: 
      {
         request->port = destination_port;
         __po_hi_msg_reallocate (&msg);
         __po_hi_marshall_request (request, &msg);

#ifdef __PO_HI_DEBUG
         __po_hi_messages_debug (&msg);
#endif

         len = write (nodes[associated_device].socket, &(msg.content), size_to_write);

         if (len != size_to_write)
         {
            __DEBUGMSG (" [error write() length in file %s, line%d ]\n", __FILE__, __LINE__);
            close (nodes[associated_device].socket);
            nodes[associated_device].socket = -1;
            return __PO_HI_ERROR_TRANSPORT_SEND;		
         }
         break;
      }
   }

   return __PO_HI_SUCCESS;
}


void* __po_hi_sockets_poller (const __po_hi_device_id dev_id)
{
   (void) dev_id;
   __DEBUGMSG ("Poller launched, device-id=%d\n", socket_device_id);
   socklen_t          socklen = sizeof (struct sockaddr);
   /* See ACCEPT (2) for details on initial value of socklen */

   __po_hi_uint32_t   len;
   int                sock;
   int                max_socket;
   fd_set             selector;
   struct sockaddr_in sa;
   __po_hi_device_id  dev;
   __po_hi_node_t     dev_init;
   __po_hi_request_t  received_request;
   __po_hi_msg_t      msg;
   int                established = 0; 

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
      if (dev != socket_device_id)
      {
         __DEBUGMSG ("[DRIVER SOCKETS] Poller waits for connection with device %d\n", dev);

         /*
         __PO_HI_SET_SOCKET_TIMEOUT(nodes[socket_device_id].socket,5);
         */

         established = 0;

         while (established == 0)
         {
            sock = accept (nodes[socket_device_id].socket, (struct sockaddr*) &sa, &socklen);

            __PO_HI_SET_SOCKET_TIMEOUT(sock,10);

#ifndef __PO_HI_USE_PROTOCOL_MYPROTOCOL_I
            if (read (sock, &dev_init, sizeof (__po_hi_device_id)) != sizeof (__po_hi_device_id))
            {
               established = 0;
               __DEBUGMSG ("[DRIVER SOCKETS] Cannot read device-id for device %d, socket=%d\n", dev, sock);
            }
            else
            {
               __DEBUGMSG ("[DRIVER SOCKETS] read device-id %d from socket=%d\n", dev_init, sock);
               established = 1;
            }
#else
            established = 1;
#endif
         }
         rnodes[dev].socket = sock;
         if (sock > max_socket )
         {
            max_socket = sock;
         }	  
      }
   }
   __DEBUGMSG ("[DRIVER SOCKETS] Poller initialization finished, waiting for other tasks\n");
   __po_hi_wait_initialization ();
   __DEBUGMSG ("[DRIVER SOCKETS] Other tasks are initialized, let's start the polling !\n");

   /*
    * Then, listen and receive data on the socket, identify the node
    * which send the data and put it in its message queue
    */
   while (1)
   {
      FD_ZERO( &selector );
      for (dev = 0; dev < __PO_HI_NB_DEVICES ; dev++)
      {
         if ( (dev != socket_device_id ) && ( rnodes[dev].socket != -1 ) )
         {
            FD_SET( rnodes[dev].socket , &selector );
         }
      }

      if (select (max_socket + 1, &selector, NULL, NULL, NULL) == -1 )
      {
#ifdef __PO_HI_DEBUG
         __DEBUGMSG ("[DRIVER SOCKETS] Error on select for node %d\n", __po_hi_mynode);
#endif 
      }
#ifdef __PO_HI_DEBUG
      __DEBUGMSG ("[DRIVER SOCKETS] Receive message\n");
#endif

      for (dev = 0; dev < __PO_HI_NB_DEVICES ; dev++)
      {
         __DEBUGMSG ("[DRIVER SOCKETS] Try to watch if it comes from device %d (socket=%d)\n", dev, rnodes[dev].socket);
         if ( (rnodes[dev].socket != -1 ) && FD_ISSET(rnodes[dev].socket, &selector))
         {
            __DEBUGMSG ("[DRIVER SOCKETS] Receive message from dev %d\n", dev);
            memset (msg.content, '\0', __PO_HI_MESSAGES_MAX_SIZE);
            len = recv (rnodes[dev].socket, msg.content, __PO_HI_MESSAGES_MAX_SIZE, MSG_WAITALL);
            msg.length = len;
            __DEBUGMSG ("[DRIVER SOCKETS] Message received len=%d\n",(int)len);

#ifdef __PO_HI_DEBUG
   __po_hi_messages_debug (&msg);
#endif


            if (len == 0)
            {

               __DEBUGMSG ("[DRIVER SOCKETS] Zero size from device %d\n",dev);
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


/*
 * Old receiver code that is based on PolyORB-HI-C for AADLv1
 * Would be considered as deprecated.
 */
void* __po_hi_sockets_receiver_task (void)
{
   socklen_t          socklen = sizeof (struct sockaddr);
   /* See ACCEPT (2) for details on initial value of socklen */

   __po_hi_uint32_t           len;
   int                        sock;
   int                        max_socket;
   fd_set                     selector;
   __po_hi_msg_t              msg;
   __po_hi_node_t             node;
   __po_hi_node_t             node_init;
   __po_hi_request_t          received_request;
   struct sockaddr_in         sa;
   __po_hi_protocol_conf_t*   protocol_conf;


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
      if (node != __po_hi_mynode )
      {
         sock = accept (nodes[__po_hi_mynode].socket, (struct sockaddr*) &sa, &socklen);
         if (sock == -1)
         {
            __DEBUGMSG ("accept() failed, return=%d\n", sock);
         }

         __DEBUGMSG ("accept() success, return=%d\n", sock);

#ifndef __PO_HI_USE_PROTOCOL_MYPROTOCOL_I
         if (read (sock, &node_init, sizeof (__po_hi_node_t)) != sizeof (__po_hi_node_t))
         {
            __DEBUGMSG ("Cannot read node-id for socket %d\n", sock);
            continue;
         }
#endif

         rnodes[node].socket = sock;
         if (sock > max_socket )
         {
            max_socket = sock;
         }	  
      }
   }
   __DEBUGMSG ("Receiver initialization finished\n");
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
         if ( (node != __po_hi_mynode ) && ( rnodes[node].socket != -1 ) )
         {
            FD_SET( rnodes[node].socket , &selector );
         }
      }

      if (select (max_socket + 1, &selector, NULL, NULL, NULL) == -1 )
      {
#ifdef __PO_HI_DEBUG
         __DEBUGMSG ("Error on select for node %d\n", __po_hi_mynode);
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

#ifdef __PO_HI_USE_PROTOCOL_MYPROTOCOL_I

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


            protocol_conf = __po_hi_transport_get_protocol_configuration (virtual_bus_myprotocol_i);
            protocol_conf->unmarshaller (&received_request, &msg);
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
#endif

            __po_hi_main_deliver (&received_request);

            __po_hi_msg_reallocate(&msg);        /* re-initialize the message */
         }
      }
   }  
   return NULL;
}

void __po_hi_driver_sockets_init (__po_hi_device_id id)
{
   int                i;
   int                ret;
   int                reuse;
   char               *tmp;
   __po_hi_uint16_t   dev;
   __po_hi_time_t     mytime;
   __po_hi_time_t     tmptime;
   __po_hi_time_t     current_time;
   struct sockaddr_in sa;
   struct hostent*    hostinfo;


   __po_hi_c_ip_conf_t* ipconf;
   char ip_addr[16];
   int ip_port;
   int node;

   socket_device_id = id;

   for (node = 0 ; node < __PO_HI_NB_DEVICES ; node++)
   {
      nodes[node].socket = -1;
   }

   ipconf = (__po_hi_c_ip_conf_t*)__po_hi_get_device_configuration (id);
   ip_port = (int)ipconf->port;

   __DEBUGMSG ("My configuration, addr=%s, port=%lld\n", ipconf->address, ipconf->port );

   /*
    * If the current node port has a port number, then it has to
    * listen to other nodes. So, we create a socket, bind it and
    * listen to other nodes.
    */
   if (ip_port != 0)
   {
      nodes[id].socket = socket (AF_INET, SOCK_STREAM, 0);

      if (nodes[id].socket == -1 )
      {
#ifdef __PO_HI_DEBUG
         __DEBUGMSG ("Cannot create socket for device %d\n", id);
#endif
         return;
      }

      reuse = 1;
      setsockopt (nodes[id].socket, SOL_SOCKET, SO_REUSEADDR, &reuse, sizeof (reuse));

      sa.sin_addr.s_addr = htonl (INADDR_ANY);   /* We listen on all adresses */
      sa.sin_family = AF_INET;                   
      sa.sin_port = htons (ip_port);   /* Port provided by the generated code */

      if( bind( nodes[id].socket , ( struct sockaddr * ) &sa , sizeof( struct sockaddr_in ) ) < 0 )
      {
#ifdef __PO_HI_DEBUG
         __DEBUGMSG ("Unable to bind socket and port on socket %d\n", nodes[id].socket);
#endif
      }

      if( listen( nodes[id].socket , __PO_HI_NB_ENTITIES ) < 0 )
      {
#ifdef __PO_HI_DEBUG
         __DEBUGMSG ("Cannot listen on socket %d\n", nodes[id].socket);
#endif
      }

      /* 
       * Create the thread which receive all data from other
       * nodes. This thread will execute the function
       * __po_hi_receiver_task
       */

      __po_hi_initialize_add_task ();

      __po_hi_create_generic_task 
         (-1, 0,__PO_HI_MAX_PRIORITY, 0, __po_hi_sockets_poller);
   }

   /*
    * For each node in the sytem that may communicate with the current
    * node we create a socket. This socket will be used to send data.
    */
   for (dev = 0 ; dev < __PO_HI_NB_DEVICES ; dev++ )
   {
      if (dev == id)
      {
         continue;
      }

      __DEBUGMSG ("[DRIVER SOCKETS] Will initialize connection with device %d\n", dev);

      memset (ip_addr, '\0', 16);
      ip_port = 0;

      ipconf = (__po_hi_c_ip_conf_t*) __po_hi_get_device_configuration (dev);
      ip_port = (int)ipconf->port;

      __DEBUGMSG ("[DRIVER SOCKETS] Configuration for device %d, addr=%s, port=%d\n", dev, ipconf->address, ip_port);

      if (ip_port == 0)
      {
         __DEBUGMSG ("[DRIVER SOCKETS] Invalid remote port\n");
         continue;
      }

      while (1)
      {
         nodes[dev].socket = socket (AF_INET, SOCK_STREAM, 0);

         if (nodes[dev].socket == -1 )
         {
            __DEBUGMSG ("[DRIVER SOCKETS] Socket for dev %d is not created\n", dev);
            return;
         }

         __DEBUGMSG ("[DRIVER SOCKETS] Socket for dev %d created, value=%d\n", dev, nodes[dev].socket);

         hostinfo = gethostbyname ((char*)ipconf->address);

         if (hostinfo == NULL )
         {
            __DEBUGMSG ("[DRIVER SOCKETS] Error while getting host informations for device %d\n", dev);
         }

         sa.sin_port = htons (ip_port);
         sa.sin_family = AF_INET;

         /* The following lines are used to copy the
          * hostinfo->h_length to the sa.sin_addr member. Most
          * of program use the memcpy to do that, but the
          * RT-POSIX profile we use forbid the use of this
          * function.  We use a loop instead to perform the
          * copy.  So, these lines replace the code :
          *
          * memcpy( (char*) &( sa.sin_addr ) , (char*)hostinfo->h_addr , hostinfo->h_length );
          */

         tmp = (char*) &(sa.sin_addr);
         for (i=0 ; i<hostinfo->h_length ; i++)
         {
            tmp[i] = hostinfo->h_addr[i];
         }

         /*
          * We try to connect on the remote host. We try every
          * second to connect on.
         __PO_HI_SET_SOCKET_TIMEOUT(nodes[dev].socket,5);
          */

         ret = connect (nodes[dev].socket, 
                        (struct sockaddr*) &sa ,
                        sizeof (struct sockaddr_in));

#ifdef __PO_HI_USE_PROTOCOL_MYPROTOCOL_I
         if (ret == 0)
         {
            __DEBUGMSG ("[DRIVER SOCKETS] Connection established with device %d, socket=%d\n", dev, nodes[dev].socket);

            break;
         }
         else
         {
            __DEBUGMSG ("connect() failed, return=%d\n", ret);
         }

#else
         if (ret == 0)
         {

            __DEBUGMSG ("[DRIVER SOCKETS] Send my id (%d)\n", id);
            if (write (nodes[dev].socket, &id, sizeof (__po_hi_device_id)) != sizeof (__po_hi_device_id))
            {
               __DEBUGMSG ("[DRIVER SOCKETS] Device %d cannot send his id\n", id);
            }
            __DEBUGMSG ("[DRIVER SOCKETS] Connection established with device %d, socket=%d\n", dev, nodes[dev].socket);
            break;
         }
         else
         {
            __DEBUGMSG ("connect() failed, return=%d\n", ret);
         }
#endif

         if (close (nodes[dev].socket))
         {
            __DEBUGMSG ("[DRIVER SOCKETS] Cannot close socket %d\n", nodes[dev].socket);
         }

         /*
          * We wait 500ms each time we try to connect on the
          * remote host
          */

         __po_hi_get_time (&current_time);
         __po_hi_milliseconds (&tmptime, 500);
         __po_hi_add_times (&mytime, &current_time, &tmptime);
         __DEBUGMSG ("[DRIVER SOCKETS] Cannot connect on device %d, wait 500ms\n", dev);
         __po_hi_delay_until (&mytime);
      }
   }

}

#endif

