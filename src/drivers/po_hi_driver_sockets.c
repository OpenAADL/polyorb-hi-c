/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2010-2017 ESA & ISAE.
 */

#include <deployment.h>
#include <marshallers.h>

#if (defined (__PO_HI_NEED_DRIVER_SOCKETS) || \
     defined (__PO_HI_NEED_DRIVER_RTEMS_NE2000_SOCKETS))

#ifdef _WIN32
#include <winsock2.h>
#endif

#include <po_hi_config.h>
#include <po_hi_utils.h>
#include <po_hi_task.h>
#include <po_hi_transport.h>
#include <po_hi_debug.h>
#include <po_hi_types.h>
#include <po_hi_messages.h>
#include <po_hi_monitor.h>
#include <po_hi_returns.h>
#include <po_hi_main.h>
#include <po_hi_task.h>
#include <po_hi_gqueue.h>
#include <drivers/po_hi_driver_sockets.h>

#include <activity.h>

#include <signal.h>
#include <string.h>
#include <unistd.h>
#include <assert.h>
#ifndef _WIN32
#include <netdb.h>
#include <sys/types.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <arpa/inet.h>
#include <sys/time.h>
#endif

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

int                  __po_hi_c_sockets_listen_socket;
int                  __po_hi_c_sockets_read_sockets[__PO_HI_NB_DEVICES];
int                  __po_hi_c_sockets_write_sockets[__PO_HI_NB_DEVICES];
__po_hi_request_t    __po_hi_c_sockets_poller_received_request;
__po_hi_msg_t        __po_hi_c_sockets_poller_msg;
__po_hi_msg_t        __po_hi_c_sockets_send_msg;
__po_hi_device_id    __po_hi_c_sockets_device_id;

int      __po_hi_c_sockets_array_init_done = 0;

int __po_hi_driver_sockets_send (__po_hi_task_id task_id,
                                 __po_hi_port_t port)
{
   int                        size_to_write;
#ifndef _WIN32
   int                        optval = 0;
   socklen_t                  optlen = 0;
#else
   char FAR                   optval = 0;
   int FAR                    optlen = 0;
#endif
   __po_hi_device_id          remote_device;
   __po_hi_device_id          local_device;
   __po_hi_local_port_t       local_port;
   __po_hi_request_t*         request;
   __po_hi_port_t             destination_port;
   __po_hi_protocol_t         protocol_id;
   __po_hi_protocol_conf_t*   protocol_conf;
   __po_hi_monitor_status_t   device_status;

   local_port              = __po_hi_get_local_port_from_global_port (port);
   request                 = __po_hi_gqueue_get_most_recent_value (task_id, local_port);
   destination_port        = __po_hi_gqueue_get_destination (task_id, local_port, 0);
   local_device            = __po_hi_get_device_from_port (port);
   remote_device           = __po_hi_get_device_from_port (destination_port);
   protocol_id             = __po_hi_transport_get_protocol (port, destination_port);
   protocol_conf           = __po_hi_transport_get_protocol_configuration (protocol_id);

   __DEBUGMSG ("[DRIVER SOCKETS] Try to write from task=%d, port=%d, local_device=%d, remote device=%d, socket=%d\n", task_id, port, local_device, remote_device, __po_hi_c_sockets_write_sockets[remote_device]);
   if (request->port == -1)
   {
      __DEBUGMSG (" [DRIVER SOCKETS] No data to write on port %d\n", port);
      return __PO_HI_ERROR_TRANSPORT_SEND;
   }

#if __PO_HI_MONITOR_ENABLED
   if (__po_hi_monitor_get_status_device (local_device, &device_status) != __PO_HI_SUCCESS)
   {
      __DEBUGMSG ("[DRIVER SOCKETS] Cannot get the status of device %d\n", local_device);
      return __PO_HI_ERROR_TRANSPORT_SEND;
   }

   if (device_status.status != po_hi_monitor_status_ok)
   {
      __DEBUGMSG ("[DRIVER SOCKETS] Device has a problem and is not able to process the request, aborting (device-id=%d, status= %d)\n", local_device, device_status.status);
      return __PO_HI_ERROR_TRANSPORT_SEND;
   }
#endif

   if (__po_hi_c_sockets_write_sockets[remote_device] == -1 )
   {
#ifdef __PO_HI_DEBUG
      __DEBUGMSG (" [DRIVER SOCKETS] Invalid socket for port-id %d, device-id %d\n", destination_port, remote_device);
#endif
      return __PO_HI_ERROR_TRANSPORT_SEND;
   }

   /*
    * After sending the entity identifier, we send the message which
    * contains the request.
    */

   size_to_write = __PO_HI_MESSAGES_MAX_SIZE;

   if (getsockopt (__po_hi_c_sockets_write_sockets[remote_device], SOL_SOCKET, SO_ERROR, &optval, &optlen) == -1)
   {
      __DEBUGMSG (" [error getsockopt() in file %s, line%d ]\n", __FILE__, __LINE__);
      close (__po_hi_c_sockets_write_sockets[remote_device]);
      __po_hi_c_sockets_write_sockets[remote_device] = -1;
      return __PO_HI_ERROR_TRANSPORT_SEND;
   }

   if (optval != 0)
   {
      __DEBUGMSG (" [error getsockopt() return code in file %s, line%d ]\n", __FILE__, __LINE__);
      close (__po_hi_c_sockets_write_sockets[remote_device]);
      __po_hi_c_sockets_write_sockets[remote_device] = -1;
      return __PO_HI_ERROR_TRANSPORT_SEND;
   }

#ifndef _WIN32
   /*
    * Ignore SIGPIPE to be able to recover from
    * errors instead of crashing the node
    */

   if (signal (SIGPIPE, SIG_IGN) == SIG_ERR)
   {
      __DEBUGMSG (" [error signal() return code in file %s, line%d ]\n", __FILE__, __LINE__);
      close (__po_hi_c_sockets_write_sockets[remote_device]);
      __po_hi_c_sockets_write_sockets[remote_device] = -1;
      return __PO_HI_ERROR_TRANSPORT_SEND;
   }
#endif

   switch (protocol_id)
   {
#ifdef __PO_HI_USE_PROTOCOL_MYPROTOCOL_I
      case virtual_bus_myprotocol_i:
      {
        int  len;
        size_to_write = sizeof (int);
        int datawritten;
        protocol_conf->marshaller(request, &datawritten, &size_to_write);
#ifdef _WIN32
        len = send (__po_hi_c_sockets_write_sockets[remote_device], &datawritten, size_to_write, 0);
#else
        len = write (__po_hi_c_sockets_write_sockets[remote_device], &datawritten, size_to_write);
#endif

        if (len != size_to_write)
         {
            __DEBUGMSG (" [error write() length in file %s, line%d ]\n", __FILE__, __LINE__);
            close (__po_hi_c_sockets_write_sockets[remote_device]);
            __po_hi_c_sockets_write_sockets[remote_device] = -1;
            return __PO_HI_ERROR_TRANSPORT_SEND;
         }
         break;
      }
#endif
      case invalid_protocol:
      default:
      {

	 request->port = destination_port;
         __po_hi_msg_reallocate (&__po_hi_c_sockets_send_msg);
         __po_hi_marshall_request (request, &__po_hi_c_sockets_send_msg);

#ifdef __PO_HI_DEBUG
         __po_hi_messages_debug (&__po_hi_c_sockets_send_msg[remote_device]);
#endif
         if (__po_hi_c_sockets_write_sockets[remote_device] != -1)
         {
	    int  len;
#ifdef _WIN32
            len = send (__po_hi_c_sockets_write_sockets[remote_device], (char*) &(__po_hi_c_sockets_send_msg.content), size_to_write, 0);
#else
            len = write (__po_hi_c_sockets_write_sockets[remote_device], &(__po_hi_c_sockets_send_msg.content), size_to_write);
#endif

            if (len != size_to_write)
            {

#if __PO_HI_MONITOR_ENABLED
               __po_hi_monitor_report_failure_device (remote_device, po_hi_monitor_failure_value);
#endif

               __DEBUGMSG (" [error write() length in file %s, line%d ]\n", __FILE__, __LINE__);
               close (__po_hi_c_sockets_write_sockets[remote_device]);
               __po_hi_c_sockets_write_sockets[remote_device] = -1;
               return __PO_HI_ERROR_TRANSPORT_SEND;
            }
         }

         request->port = __PO_HI_GQUEUE_INVALID_PORT;
         break;
      }
   }

   return __PO_HI_SUCCESS;
}

/*pragma is for unused parameter "dev_id_addr"*/
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
void* __po_hi_sockets_poller (__po_hi_device_id* dev_id_addr)
{
#ifdef _WIN32
   int                        socklen;
#else
   socklen_t                  socklen;
#endif
   /* See ACCEPT (2) for details on initial value of socklen */

   int                        len;
   int                        sock;
   int                        max_socket;
   fd_set                     selector;
   struct sockaddr_in         sa;
   __po_hi_device_id          dev;
   __po_hi_node_t             dev_init;
   int                        ret;
   __po_hi_device_id          dev_id;
   __po_hi_int32_t            n_connected;

   socklen = sizeof (struct sockaddr);

   max_socket = 0; /* Used to compute the max socket number, useful for listen() call */

   dev_id = __po_hi_c_sockets_device_id;

   __DEBUGMSG ("Poller launched, device-id=%d\n", dev_id);

   n_connected = 0;

   for (dev = 0; dev < __PO_HI_NB_DEVICES ; dev++)
   {
      if (__po_hi_transport_share_bus (dev, dev_id) == 1)
      {
         n_connected++;
      }
   }

   assert (n_connected >= 0);
   __DEBUGMSG ("Number of devices that share the bus=%d\n", n_connected);


   /*
    * Create a socket for each node that will communicate with us.
    */
   for (dev = 0; dev < n_connected - 1; dev++)
   {
         int established = 0;

         while (established == 0)
         {
            __DEBUGMSG ("[DRIVER SOCKETS] Poller waits for connection with device %d (reading device=%d, socket=%d)\n", dev, dev_id, __po_hi_c_sockets_read_sockets[dev]);
            sock = accept (__po_hi_c_sockets_listen_socket, (struct sockaddr*) &sa, &socklen);

            if (sock == -1)
            {
               continue;
            }

            __DEBUGMSG ("[DRIVER SOCKETS] accept() passed, waiting for device id %d\n", dev);

#ifndef __PO_HI_USE_PROTOCOL_MYPROTOCOL_I
            dev_init = 0;
#ifdef _WIN32
            ret = recv (sock, (char*) &dev_init, sizeof (__po_hi_device_id), 0);
#else
            ret = read (sock, &dev_init, sizeof (__po_hi_device_id));
#endif

            if (ret != sizeof (__po_hi_device_id))
            {
               established = 0;
               __DEBUGMSG ("[DRIVER SOCKETS] Cannot read device-id for device %d, socket=%d, ret=%d, read size=%d, expected size=%lu\n", dev, sock, ret, ret, sizeof (__po_hi_device_id));
            }
            else
            {
               dev_init = __po_hi_swap_byte (dev_init);

               __DEBUGMSG ("[DRIVER SOCKETS] read device-id %d from socket=%d\n", dev_init, sock);
               established = 1;
            }
#else
            established = 1;
            dev_init = dev;
#endif
         }
         __po_hi_c_sockets_read_sockets[dev_init] = sock;
         if (sock > max_socket )
         {
            max_socket = sock;
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
         if ( (dev != dev_id ) && ( __po_hi_c_sockets_read_sockets[dev] != -1 ) )
         {

            __DEBUGMSG ("[DRIVER SOCKETS] Add socket %d to the selector\n", __po_hi_c_sockets_read_sockets[dev]);
            FD_SET( __po_hi_c_sockets_read_sockets[dev], &selector );
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
         __DEBUGMSG ("[DRIVER SOCKETS] Try to watch if it comes from device %d (socket=%d)\n", dev, __po_hi_c_sockets_read_sockets[dev]);
         if ( (__po_hi_c_sockets_read_sockets[dev] != -1 ) && FD_ISSET(__po_hi_c_sockets_read_sockets[dev], &selector))
         {
            __DEBUGMSG ("[DRIVER SOCKETS] Receive message from dev %d\n", dev);
#ifdef __PO_HI_USE_PROTOCOL_MYPROTOCOL_I
            {

               protocol_conf = __po_hi_transport_get_protocol_configuration (virtual_bus_myprotocol_i);

               int datareceived;
               len = recv (__po_hi_c_sockets_read_sockets[dev], &datareceived, sizeof (int), MSG_WAITALL);
               __DEBUGMSG ("[DRIVER SOCKETS] Message received len=%d\n",(int)len);
               if (len == 0)
               {
                  __DEBUGMSG ("[DRIVER SOCKETS] Zero size from device %d\n",dev);
                  __po_hi_c_sockets_read_sockets[dev] = -1;
                  continue;
               }
               protocol_conf->unmarshaller (&__po_hi_c_sockets_poller_received_request, &datareceived, len);
               __po_hi_c_sockets_poller_received_request.port = 1;
            }

#else
            memset (__po_hi_c_sockets_poller_msg.content, '\0', __PO_HI_MESSAGES_MAX_SIZE);


#ifdef _WIN32
            len = recv (__po_hi_c_sockets_read_sockets[dev], __po_hi_c_sockets_poller_msg.content, __PO_HI_MESSAGES_MAX_SIZE, 0);
#else
            len = recv (__po_hi_c_sockets_read_sockets[dev], __po_hi_c_sockets_poller_msg.content, __PO_HI_MESSAGES_MAX_SIZE, MSG_WAITALL);
#endif

            __po_hi_c_sockets_poller_msg.length = len;
            __DEBUGMSG ("[DRIVER SOCKETS] Message received len=%d\n",(int)len);

#ifdef __PO_HI_DEBUG
   __po_hi_messages_debug (&__po_hi_c_sockets_poller_msg);
#endif

            if (len <= 0)
            {
               __DEBUGMSG ("[DRIVER SOCKETS] Invalid size (%d) from device %d\n",len, dev);
               __po_hi_c_sockets_read_sockets[dev] = -1;
               continue;
            }

            __po_hi_unmarshall_request (&__po_hi_c_sockets_poller_received_request, &__po_hi_c_sockets_poller_msg);
#endif
	    __DEBUGMSG ("[DRIVER SOCKETS] Delivering message to %d\n",__po_hi_c_sockets_poller_received_request.port );
            __po_hi_main_deliver (&__po_hi_c_sockets_poller_received_request);
         }
      }
   }
   return NULL;
}
#pragma GCC diagnostic pop


void __po_hi_driver_sockets_init (__po_hi_device_id dev_id)
{
   int                     ret;
#ifdef _WIN32
   char FAR                reuse;
#else
   int                     reuse;
#endif
   struct sockaddr_in      sa;
   unsigned short          ip_port;

   __po_hi_c_ip_conf_t*    ipconf;
   __po_hi_device_id       dev;

   __po_hi_device_id          sent_id;
   struct hostent*            hostinfo;

   __po_hi_time_t             mytime;
   __po_hi_time_t             tmptime;

   char                       *tmp;
   __po_hi_time_t             current_time;
   int                        i;

   __po_hi_c_sockets_listen_socket = -1;

   __po_hi_c_sockets_device_id     = dev_id;

   if (__po_hi_c_sockets_array_init_done == 0)
   {
      for (dev = 0 ; dev < __PO_HI_NB_DEVICES ; dev++)
      {
         __po_hi_c_sockets_read_sockets[dev]   = -1;
         __po_hi_c_sockets_write_sockets[dev]  = -1;
      }

      __po_hi_c_sockets_array_init_done = 1;
   }

   __po_hi_transport_set_sending_func (dev_id, __po_hi_driver_sockets_send);

   ipconf = (__po_hi_c_ip_conf_t*)__po_hi_get_device_configuration (dev_id);
   ip_port = ipconf->port;

   __DEBUGMSG ("My configuration, addr=%s, port=%d\n", ipconf->address, ip_port );

   /*
    * If the current node port has a port number, then it has to
    * listen to other nodes. So, we create a socket, bind it and
    * listen to other nodes.
    */
   if (ip_port != 0)
   {
      __po_hi_c_sockets_listen_socket = socket (AF_INET, SOCK_STREAM, 0);


      if (__po_hi_c_sockets_listen_socket == -1 )
      {
#ifdef __PO_HI_DEBUG
         __DEBUGMSG ("Cannot create socket for device %d\n", dev_id);
#endif
         return;
      }

      __DEBUGMSG ("Socket created for addr=%s, port=%d, socket value=%d\n", ipconf->address, ip_port, __po_hi_c_sockets_listen_socket);

      reuse = 1;

      if (setsockopt (__po_hi_c_sockets_listen_socket, SOL_SOCKET, SO_REUSEADDR, &reuse, sizeof (reuse)))
      {
         __DEBUGMSG ("[DRIVER SOCKETS] Error while making the receiving socket reusable\n");
      }

      sa.sin_addr.s_addr = htonl (INADDR_ANY);   /* We listen on all adresses */
      sa.sin_family = AF_INET;
      sa.sin_port = htons (ip_port);   /* Port provided by the generated code */

      if( bind (__po_hi_c_sockets_listen_socket, (struct sockaddr *) &sa , sizeof (struct sockaddr_in) ) < 0 )
      {
         __DEBUGMSG ("Unable to bind socket and port on socket %d\n", __po_hi_c_sockets_listen_socket);
      }

      if( listen (__po_hi_c_sockets_listen_socket, __PO_HI_NB_DEVICES) < 0 )
      {
         __DEBUGMSG ("Cannot listen on socket %d\n", __po_hi_c_sockets_listen_socket);
      }

      /*
       * Create the thread which receive all data from other
       * nodes. This thread will execute the function
       * __po_hi_receiver_task
       */

      __po_hi_initialize_add_task ();
      __po_hi_create_generic_task
	(-1, 0,__PO_HI_MAX_PRIORITY, 0, 0, (void* (*)(void))__po_hi_sockets_poller, &dev_id);
      /* For now, we force affinity to 0 */
   }


   /*
    * For each node in the sytem that may communicate with the current
    * node we create a socket. This socket will be used to send data.
    */
   for (dev = 0 ; dev < __PO_HI_NB_DEVICES ; dev++)
   {
      if (dev == dev_id)
      {
         continue;
      }

      if (__po_hi_transport_share_bus (dev, dev_id) == 0)
      {
         __DEBUGMSG ("[DRIVER SOCKETS] Device %d and device %d does not share the same bus, skip connecting them\n", dev, dev_id);
         continue;
      }

      __DEBUGMSG ("[DRIVER SOCKETS] Will initialize connection with device %d\n", dev);

      ipconf = (__po_hi_c_ip_conf_t*) __po_hi_get_device_configuration (dev);
      ip_port = (unsigned short)ipconf->port;

      __DEBUGMSG ("[DRIVER SOCKETS] Configuration for device %d, port=%d\n", dev, ip_port);

      if (ip_port == 0)
      {
         __DEBUGMSG ("[DRIVER SOCKETS] Invalid remote port\n");
         continue;
      }

      while (1)
      {
         __po_hi_c_sockets_write_sockets[dev] = socket (AF_INET, SOCK_STREAM, 0);

         if (__po_hi_c_sockets_write_sockets[dev] == -1 )
         {
            __DEBUGMSG ("[DRIVER SOCKETS] Socket for dev %d is not created\n", dev);
            return;
         }

	 int NoDelayFlag = 1;
	 if(setsockopt(__po_hi_c_sockets_write_sockets[dev],IPPROTO_TCP,TCP_NODELAY,&NoDelayFlag,sizeof(NoDelayFlag))){
	   __DEBUGMSG ("[DRIVER SOCKETS] Unable to set TCP_NODELAY for dev %d\n", dev);
	 }

         __DEBUGMSG ("[DRIVER SOCKETS] Socket for dev %d created, value=%d\n", dev, __po_hi_c_sockets_write_sockets[dev]);

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
          */
         __PO_HI_SET_SOCKET_TIMEOUT(__po_hi_c_sockets_write_sockets[dev], 500000);
         ret = connect (__po_hi_c_sockets_write_sockets[dev],
                        (struct sockaddr*) &sa ,
                        sizeof (struct sockaddr_in));

#ifdef __PO_HI_USE_PROTOCOL_MYPROTOCOL_I
         if (ret == 0)
         {
            __DEBUGMSG ("[DRIVER SOCKETS] Connection established with device %d, socket=%d\n", dev, __po_hi_c_sockets_write_sockets[dev]);

            break;
         }
         else
         {
            __DEBUGMSG ("connect() failed, return=%d\n", ret);
         }

#else
         if (ret == 0)
         {
            __DEBUGMSG ("[DRIVER SOCKETS] Send my id (%d) to device %d through socket %d\n", dev_id, dev , __po_hi_c_sockets_write_sockets[dev]);

            sent_id = __po_hi_swap_byte (dev_id);
#ifdef _WIN32
            ret = send (__po_hi_c_sockets_write_sockets[dev], (char*) &sent_id, sizeof (__po_hi_device_id), 0);
#else
            ret = write (__po_hi_c_sockets_write_sockets[dev], &sent_id, sizeof (__po_hi_device_id));
#endif
            if (ret != sizeof (__po_hi_device_id))
            {
               __DEBUGMSG ("[DRIVER SOCKETS] Device %d cannot send his id, expected size=%lu, return value=%d\n", dev_id, sizeof (__po_hi_device_id), ret);
            }
            else
            {
               __DEBUGMSG ("[DRIVER SOCKETS] Connection established with device %d, socket=%d\n", dev, __po_hi_c_sockets_write_sockets[dev]);

               break;
            }
         }
         else
         {
            __DEBUGMSG ("connect() failed, return=%d\n", ret);
         }
#endif

         if (close (__po_hi_c_sockets_write_sockets[dev]))
         {
            __DEBUGMSG ("[DRIVER SOCKETS] Cannot close socket %d\n", __po_hi_c_sockets_write_sockets[dev]);
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
   __DEBUGMSG ("[DRIVER SOCKETS] INITIALIZATION DONE\n");
}

#endif
