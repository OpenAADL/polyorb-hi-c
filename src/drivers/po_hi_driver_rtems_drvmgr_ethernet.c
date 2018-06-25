/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2018 ESA & ISAE.
 */

#include <stdio.h>

#include <deployment.h>

#include <po_hi_debug.h>
#include <po_hi_task.h>
#include <po_hi_types.h>
#include <po_hi_utils.h>
#include <po_hi_messages.h>
#include <po_hi_transport.h>
#include <po_hi_returns.h>
#include <po_hi_gqueue.h>
#include <po_hi_main.h>
#include <po_hi_protected.h>

#include <drivers/po_hi_driver_rasta_common.h>
#include <drivers/po_hi_rtems_utils.h>
#include <drivers/po_hi_driver_leon_eth.h>
#include <drivers/po_hi_driver_sockets.h>
#include <drivers/configuration/ip.h>
/* po-hi-c related files */

#include <activity.h>
#include <marshallers.h>
#include <deployment.h>
/* generated files */

#include <termios.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>
#include <signal.h>
#include <netdb.h>
#include <arpa/inet.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <netinet/in.h>

#include <po_hi_driver_drvmgr_common.h>
/* Common drvmgr initialization */

__po_hi_inetnode_t nodes[__PO_HI_NB_DEVICES];
__po_hi_inetnode_t rnodes[__PO_HI_NB_DEVICES];

__po_hi_device_id leon_eth_device_id;

#define __PO_HI_SET_SOCKET_TIMEOUT(mysocket,nsec) { struct timeval timeout; \
    timeout.tv_sec = nsec;						\
    timeout.tv_usec = 0;						\
    setsockopt (mysocket, SOL_SOCKET, SO_RCVTIMEO, (char *)&timeout,sizeof (timeout)); }

#if ((defined GRLEON3)||((defined GRLEON2)&&(RTEMS412)))

#define RTEMS_BSP_NETWORK_DRIVER_ATTACH RTEMS_BSP_NETWORK_DRIVER_ATTACH_GRETH

#define RTEMS_BSP_NETWORK_DRIVER_NAME RTEMS_BSP_NETWORK_DRIVER_NAME_GRETH

#elif GRLEON2

#define RTEMS_BSP_NETWORK_DRIVER_ATTACH RTEMS_BSP_NETWORK_DRIVER_ATTACH_SMC91111

#define RTEMS_BSP_NETWORK_DRIVER_NAME "open_eth1"

#endif

#include <bsp.h>
#include <rtems/rtems_bsdnet.h>

#include <bsp/network_interface_add.h>

#ifdef RTEMS_USE_LOOPBACK
/*
 * Loopback interface
 */
extern void rtems_bsdnet_loopattach();
static struct rtems_bsdnet_ifconfig loopback_config = {
        "lo0",				/* name */
        rtems_bsdnet_loopattach,	/* attach function */

        NULL,				/* link to next interface */

        "127.0.0.1",			/* IP address */
        "255.0.0.0",			/* IP net mask */
};
#endif

/*
 * Network configuration
 */
struct rtems_bsdnet_config rtems_bsdnet_config = {
#ifdef RTEMS_USE_LOOPBACK
        &loopback_config,		/* link to next interface */
#else
        NULL,				/* No more interfaces */
#endif

#if (defined (RTEMS_USE_BOOTP))
        rtems_bsdnet_do_bootp,
#else
        NULL,
#endif

        64,			/* Default network task priority */
        128*1024,		/* Default mbuf capacity */
        256*1024,		/* Default mbuf cluster capacity */

#if (!defined (RTEMS_USE_BOOTP))
        "rtems_host",		/* Host name */
        "localnet",		/* Domain name */
        "192.168.0.1",		/* Gateway */
        "192.168.0.1",		/* Log host */
        {"192.168.0.1" },	/* Name server(s) */
        {"192.168.0.1" },	/* NTP server(s) */

#endif /* !RTEMS_USE_BOOTP */

};

/* Table used by network interfaces that register themselves using the
 * network_interface_add routine. From this table the IP address, netmask
 * and Ethernet MAC address of an interface is taken.
 *
 * The network_interface_add routine puts the interface into the
 * rtems_bsnet_config.ifconfig list.
 *
 * Set IP Address and Netmask to NULL to select BOOTP.
 */
struct ethernet_config interface_configs[] =
{
        { "192.168.0.42", "255.255.255.0", {0x00, 0x80, 0x7F, 0x22, 0x61, 0x79}},
        { "192.168.1.67", "255.255.255.0", {0x00, 0x80, 0x7F, 0x22, 0x61, 0x7A}},
        { "192.168.2.67", "255.255.255.0", {0x00, 0x80, 0x7F, 0x22, 0x61, 0x7B}},
        { "192.168.3.67", "255.255.255.0", {0x00, 0x80, 0x7F, 0x22, 0x61, 0x7C}},
        { "192.168.4.67", "255.255.255.0", {0x00, 0x80, 0x7F, 0x22, 0x61, 0x7D}},
        { "192.168.5.67", "255.255.255.0", {0x00, 0x80, 0x7F, 0x22, 0x61, 0x7E}},
        { "192.168.6.67", "255.255.255.0", {0x00, 0x80, 0x7F, 0x22, 0x61, 0x7F}},
        {NULL, NULL, {0,0,0,0,0,0}}
};
#define INTERFACE_CONFIG_CNT (sizeof(interface_configs)/sizeof(struct ethernet_config) - 1)

/*
 * For TFTP test application
 */
#if (defined (RTEMS_USE_BOOTP))
#define RTEMS_TFTP_TEST_HOST_NAME "BOOTP_HOST"
#define RTEMS_TFTP_TEST_FILE_NAME "BOOTP_FILE"
#else
#define RTEMS_TFTP_TEST_HOST_NAME "XXX.YYY.ZZZ.XYZ"
#define RTEMS_TFTP_TEST_FILE_NAME "tftptest"
#endif


/******************************************************************************/
__po_hi_request_t          __po_hi_c_driver_rtems_drvmgr_ethernet_poller_received_request;
__po_hi_msg_t              __po_hi_c_driver_rtems_drvmgr_ethernet_poller_msg;
__po_hi_mutex_t            __po_hi_c_rtems_ethernet_send_mutex;

void __po_hi_c_driver_rtems_drvmgr_ethernet_poller (const __po_hi_device_id dev_id)
{
   (void)                     dev_id;
   __DEBUGMSG ("Poller launched, device-id=%d\n", leon_eth_device_id);
   socklen_t                  socklen = sizeof (struct sockaddr);
   /* See ACCEPT (2) for details on initial value of socklen */

   __po_hi_uint32_t           len;
   int                        sock;
   int                        max_socket;
   fd_set                     selector;
   struct sockaddr_in         sa;
   __po_hi_device_id          dev;
   __po_hi_node_t             dev_init;
   int                        established = 0;
   __po_hi_protocol_conf_t*   protocol_conf;

   max_socket = 0; /* Used to compute the max socket number, useful for listen() call */

   /*
    * We initialize each node socket with -1 value.  This value means
    * that the socket is not active.
    */
   for (dev = 0 ; dev < __PO_HI_NB_DEVICES ; dev++)
   {
      rnodes[dev].socket = -1;
   }

   __po_hi_bus_id bus_current_node, bus_connect_node;
   bus_current_node = *__po_hi_transport_get_accessed_buses(leon_eth_device_id);

   /*
    * Create a socket for each node that will communicate with us.
    */
   for (dev = 0; dev < __PO_HI_NB_DEVICES ; dev++)
   {
      if (dev != leon_eth_device_id)
      {
         bus_connect_node = *__po_hi_transport_get_accessed_buses(dev);
         if (bus_current_node == bus_connect_node)
         {
         __PO_HI_SET_SOCKET_TIMEOUT(nodes[leon_eth_device_id].socket,500000);

         established = 0;

         while (established == 0)
         {

            __DEBUGMSG ("[DRIVER ETH] Poller waits for connection with device %d on socket %d (waiting device %d)\n", dev, nodes[leon_eth_device_id].socket, leon_eth_device_id);
            sock = accept (nodes[leon_eth_device_id].socket, (struct sockaddr*) &sa, &socklen);

            if (sock == -1)
            {
               __DEBUGMSG ("[DRIVER ETH] accept() error for device %d on device %d (socket=%d)\n", dev, leon_eth_device_id, nodes[leon_eth_device_id].socket);
               continue;
            }

            __PO_HI_SET_SOCKET_TIMEOUT(sock,100000);

#ifndef __PO_HI_USE_PROTOCOL_MYPROTOCOL_I
            if (read (sock, &dev_init, sizeof (__po_hi_device_id)) != sizeof (__po_hi_device_id))
            {
               established = 0;
               __DEBUGMSG ("[DRIVER ETH] Cannot read device-id for device %d, socket=%d\n", dev, sock);
            }
            else
            {
               __DEBUGMSG ("[DRIVER ETH] read device-id %d from socket=%d\n", dev_init, sock);
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
      } /* check the bus */
      } /* check the device */
   }
   __DEBUGMSG ("[DRIVER ETH] Poller initialization finished, waiting for other tasks\n");
   __po_hi_wait_initialization ();
   __DEBUGMSG ("[DRIVER ETH] Other tasks are initialized, let's start the polling !\n");

   /*
    * Main body of the poller function: listen and receive data on the
    * socket, identify the node which send the data and put it in its
    * message queue.
    */

   while (1)
   {
      FD_ZERO( &selector );
      for (dev = 0; dev < __PO_HI_NB_DEVICES ; dev++)
      {
         if ( (dev != leon_eth_device_id ) && ( rnodes[dev].socket != -1 ) )
         {
            FD_SET( rnodes[dev].socket , &selector );
         }
      }

      if (select (max_socket + 1, &selector, NULL, NULL, NULL) == -1 )
      {
#ifdef __PO_HI_DEBUG
         __DEBUGMSG ("[DRIVER ETH] Error on select for node %d\n", __po_hi_mynode);
#endif
      }
#ifdef __PO_HI_DEBUG
      __DEBUGMSG ("[DRIVER ETH] Receive message\n");
#endif

      for (dev = 0; dev < __PO_HI_NB_DEVICES ; dev++) {
        __DEBUGMSG ("[DRIVER ETH] Try to watch if it comes from device %d (socket=%d)\n", dev, rnodes[dev].socket);
        if ( (rnodes[dev].socket != -1 ) && FD_ISSET(rnodes[dev].socket, &selector))
          {
            __DEBUGMSG ("[DRIVER ETH] Receive message from dev %d\n", dev);

#ifdef __PO_HI_USE_PROTOCOL_MYPROTOCOL_I
            {
               protocol_conf = __po_hi_transport_get_protocol_configuration (virtual_bus_myprotocol_i);

               int datareceived;
               len = recv (rnodes[dev].socket, &datareceived, sizeof (int), MSG_WAITALL);
               __DEBUGMSG ("[DRIVER ETH] Message received len=%d\n",(int)len);
               if (len == 0)
               {
                  __DEBUGMSG ("[DRIVER ETH] Zero size from device %d\n",dev);
                  rnodes[dev].socket = -1;
                  continue;
               }
               protocol_conf->unmarshaller (& __po_hi_c_driver_rtems_drvmgr_ethernet_poller_received_request, &datareceived, len);
                __po_hi_c_driver_rtems_drvmgr_ethernet_poller_received_request.port = 1;
            }

#else
            memset (__po_hi_c_driver_rtems_drvmgr_ethernet_poller_msg.content, '\0',
                    __PO_HI_MESSAGES_MAX_SIZE);

            /* In the following, we first retrieve the size of the
               payload, then the payload itself */

            int datareceived;
            len = recv (rnodes[dev].socket,
                        &datareceived, sizeof (int),
                        MSG_WAITALL);
            __DEBUGMSG ("[DRIVER SOCKETS] Waiting for a message of size=%d\n",
                        (int)datareceived);

            len = recv (rnodes[dev].socket,
                        __po_hi_c_driver_rtems_drvmgr_ethernet_poller_msg.content,
                        datareceived,
                        MSG_WAITALL);
            __po_hi_c_driver_rtems_drvmgr_ethernet_poller_msg.length = len;
            __DEBUGMSG ("[DRIVER ETH] Message received len=%d\n",(int)len);

            if (len <= 0) {
              __DEBUGMSG ("[DRIVER ETH] Zero size from device %d\n",dev);
              rnodes[dev].socket = -1;
              continue;
            }

            __po_hi_unmarshall_request
              (& __po_hi_c_driver_rtems_drvmgr_ethernet_poller_received_request,
               &__po_hi_c_driver_rtems_drvmgr_ethernet_poller_msg);
#endif

            __po_hi_main_deliver (& __po_hi_c_driver_rtems_drvmgr_ethernet_poller_received_request);
         }
      }
   }
}


__po_hi_msg_t              __po_hi_c_driver_rtems_drvmgr_ethernet_sender_msg;

int  __po_hi_c_driver_rtems_drvmgr_ethernet_sender (__po_hi_task_id task, __po_hi_port_t port)
{
   int                        len;
   int                        size_to_write;
   int                        optval = 0;
   socklen_t                  optlen = 0;

   __po_hi_device_id          associated_device;
   __po_hi_local_port_t       local_port;
   __po_hi_request_t*         request;
   __po_hi_port_t             destination_port;
   __po_hi_protocol_t         protocol_id;
   __po_hi_protocol_conf_t*   protocol_conf;

   local_port              = __po_hi_get_local_port_from_global_port (port);
   request                 = __po_hi_gqueue_get_most_recent_value (task, local_port);
   destination_port        = __po_hi_gqueue_get_destination (task, local_port, 0);
   associated_device       = __po_hi_get_device_from_port (destination_port);
   protocol_id             = __po_hi_transport_get_protocol (port, destination_port);
   protocol_conf           = __po_hi_transport_get_protocol_configuration (protocol_id);

   if (request->port == -1) {
     __DEBUGMSG (" [DRIVER SOCKETS] No data to write on port %d\n", port);
     return __PO_HI_ERROR_TRANSPORT_SEND;
   }

   if (nodes[associated_device].socket == -1 ) {
      __DEBUGMSG
        (" [DRIVER SOCKETS] Invalid socket for port-id %d, device-id %d\n",
         destination_port, associated_device);
      return __PO_HI_ERROR_TRANSPORT_SEND;
   }

   /*
    * After sending the entity identifier, we send the message which
    * contains the request.
    */

   size_to_write = __PO_HI_MESSAGES_MAX_SIZE;

   if (getsockopt (nodes[associated_device].socket,
                   SOL_SOCKET, SO_ERROR, &optval, &optlen) == -1) {
      __DEBUGMSG (" [error getsockopt() in file %s, line%d ]\n",
                  __FILE__, __LINE__);
      close (nodes[associated_device].socket);
      nodes[associated_device].socket = -1;
      return __PO_HI_ERROR_TRANSPORT_SEND;
   }

   if (optval != 0) {
     __DEBUGMSG (" [error getsockopt() return code in file %s, line%d ]\n",
                 __FILE__, __LINE__);
     close (nodes[associated_device].socket);
     nodes[associated_device].socket = -1;
      return __PO_HI_ERROR_TRANSPORT_SEND;
   }

   /* Ignore SIGPIPE to be able to recover from errors instead of
      crashing the node */

   if (signal (SIGPIPE, SIG_IGN) == SIG_ERR) {
      __DEBUGMSG (" [error signal() return code in file %s, line%d ]\n",
                  __FILE__, __LINE__);
      close (nodes[associated_device].socket);
      nodes[associated_device].socket = -1;
      return __PO_HI_ERROR_TRANSPORT_SEND;
   }

   switch (protocol_id)
   {
#ifdef __PO_HI_USE_PROTOCOL_MYPROTOCOL_I
      case virtual_bus_myprotocol_i:
      {
         size_to_write = sizeof (int);
         int datawritten;
         protocol_conf->marshaller(request, &datawritten, &size_to_write);
         len = write (nodes[associated_device].socket, &datawritten, size_to_write);

         if (len != size_to_write)
         {
            __DEBUGMSG (" [error write() length in file %s, line%d ]\n", __FILE__, __LINE__);
            close (nodes[associated_device].socket);
            nodes[associated_device].socket = -1;
            return __PO_HI_ERROR_TRANSPORT_SEND;
         }
         break;
      }
#endif

   default:
     {
       request->port = destination_port;
       __po_hi_mutex_lock
         (&__po_hi_c_rtems_ethernet_send_mutex);
       __po_hi_msg_reallocate
         (&__po_hi_c_driver_rtems_drvmgr_ethernet_sender_msg);

       __po_hi_marshall_request
         (request, &__po_hi_c_driver_rtems_drvmgr_ethernet_sender_msg);

       size_to_write =  __po_hi_msg_length
         (&__po_hi_c_driver_rtems_drvmgr_ethernet_sender_msg);

#ifdef __PO_HI_DEBUG
       __po_hi_messages_debug (&__po_hi_c_driver_rtems_drvmgr_ethernet_sender_msg);
#endif

       /* Note: in the following, we send first the size of the
          message, then the subset of the message buffer we actually
          used. */

       int msg_size_network = size_to_write;

       len = write (nodes[associated_device].socket,
                    &msg_size_network, sizeof (int));

       len = write
         (nodes[associated_device].socket,
          &(__po_hi_c_driver_rtems_drvmgr_ethernet_sender_msg.content),
          size_to_write);

       if (len != size_to_write) {
         __DEBUGMSG (" [error write() length in file %s, line%d ]\n",
                     __FILE__, __LINE__);
         close (nodes[associated_device].socket);
         nodes[associated_device].socket = -1;
         __po_hi_mutex_unlock (&__po_hi_c_rtems_ethernet_send_mutex);
         return __PO_HI_ERROR_TRANSPORT_SEND;
       }

       __po_hi_mutex_unlock (&__po_hi_c_rtems_ethernet_send_mutex);
       request->port = __PO_HI_GQUEUE_INVALID_PORT;
       break;
     }
   }

   return __PO_HI_SUCCESS;
}

void __po_hi_c_driver_rtems_drvmgr_ethernet_init (__po_hi_device_id id)
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
   unsigned short ip_port;
   int node;

   ipconf = (__po_hi_c_ip_conf_t*)__po_hi_get_device_configuration (id);

   interface_configs[0].ip_addr = ipconf->address;

   printf ("----> %s\n", interface_configs[0].ip_addr);

   if (ipconf->exist.netmask == 1) {
     interface_configs[0].ip_netmask= ipconf->netmask;
   }

   if (ipconf->exist.gateway == 1)
   {
      rtems_bsdnet_config.gateway = ipconf->gateway;
   }

   if (ipconf->exist.dns == 1)
   {
      rtems_bsdnet_config.name_server[0] = ipconf->dns;
   }

   /* Initializes drvmgr subsystem */
   __po_hi_c_driver_drvmgr_init ();

   // xxxx mf if this is not the first driver to be initialized

#if __PO_HI_DEBUG_LEVEL >= __PO_HI_DEBUG_LEVEL_DEBUG
   rtems_bsdnet_show_if_stats ();
   rtems_bsdnet_show_inet_routes ();
   rtems_bsdnet_show_ip_stats ();
   rtems_bsdnet_show_mbuf_stats ();
#endif

   leon_eth_device_id = id;
   __po_hi_mutex_init (&__po_hi_c_rtems_ethernet_send_mutex,__PO_HI_MUTEX_REGULAR, 0);
   __po_hi_transport_set_sending_func (leon_eth_device_id, __po_hi_c_driver_rtems_drvmgr_ethernet_sender);

   for (node = 0 ; node < __PO_HI_NB_DEVICES ; node++)
   {
      nodes[node].socket = -1;
   }

   ip_port = (unsigned short)ipconf->port;

   printf ("*** WARNING the IP configuration is defined in %s, check it matches your setup\n", __FILE__);

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

      __DEBUGMSG ("[DRIVER ETH] Receiving socket for device %d created, value=%d\n", id, nodes[id].socket);

      sa.sin_addr.s_addr = htonl (INADDR_ANY);   /* We listen on all adresses */
      sa.sin_family = AF_INET;
      sa.sin_port = htons (ip_port);   /* Port provided by the generated code */

      if( bind (nodes[id].socket , (struct sockaddr *) &sa , sizeof (struct sockaddr_in) ) == -1 )
      {
         __DEBUGMSG ("Unable to bind socket and port on socket %d\n", nodes[id].socket);
      }

      if( listen( nodes[id].socket , __PO_HI_NB_ENTITIES ) == -1)
      {
         __DEBUGMSG ("Cannot listen on socket %d\n", nodes[id].socket);
      }

      __DEBUGMSG ("[DRIVER ETH] Receiving socket listen on any address on port %d\n", sa.sin_port);

      /*
       * Create the thread which receive all data from other
       * nodes. This thread will execute the function
       * __po_hi_receiver_task
       */

      __po_hi_initialize_add_task ();

//       __po_hi_create_generic_task
//         (-1, 0,__PO_HI_MAX_PRIORITY, 0, 0, (void* (*)(void)) __po_hi_c_driver_rtems_drvmgr_ethernet_poller, NULL);
      __po_hi_create_generic_task(-1, 0, 2, 2*RTEMS_MINIMUM_STACK_SIZE, 0, (void* (*)(void)) __po_hi_c_driver_rtems_drvmgr_ethernet_poller, NULL);
   }

   /*
    * For each node in the sytem that may communicate with the current
    * node we create a socket. This socket will be used to send data.
    */
   __po_hi_bus_id bus_current_node, bus_connect_node;

   bus_current_node = *__po_hi_transport_get_accessed_buses(id);

   __DEBUGMSG("[DRIVER ETH] Device %d is connected to bus: %d\n", id,bus_current_node);

   for (dev = 0 ; dev < __PO_HI_NB_DEVICES ; dev++ )
   {
      if (dev == id)
      {
         continue;
      }

      bus_connect_node= *__po_hi_transport_get_accessed_buses(dev);

      __DEBUGMSG("[DRIVER ETH] Device %d is connected to bus: %d\n", dev, bus_connect_node);

      if (bus_current_node != bus_connect_node)
      {
         continue;
      }

      __DEBUGMSG ("[DRIVER ETH] Will initialize connection with device %d\n", dev);

      memset (ip_addr, '\0', 16);
      ip_port = 0;

      ipconf = (__po_hi_c_ip_conf_t*) __po_hi_get_device_configuration (dev);
      ip_port = (unsigned short)ipconf->port;

      __DEBUGMSG ("[DRIVER ETH] Configuration for device %d, addr=%s, port=%d\n", dev, ipconf->address, ip_port);

      if (ip_port == 0)
      {
         __DEBUGMSG ("[DRIVER ETH] Invalid remote port\n");
         continue;
      }

      while (1)
      {
         nodes[dev].socket = socket (AF_INET, SOCK_STREAM, 0);

         if (nodes[dev].socket == -1 )
         {
            __DEBUGMSG ("[DRIVER ETH] Socket for dev %d is not created\n", dev);
            return;
         }

         __DEBUGMSG ("[DRIVER ETH] Socket for dev %d created, value=%d\n", dev, nodes[dev].socket);

         hostinfo = gethostbyname ((char*)ipconf->address);

         if (hostinfo == NULL )
         {
            __DEBUGMSG ("[DRIVER ETH] Error while getting host informations for device %d\n", dev);
         }

         __DEBUGMSG ("[DRIVER ETH] Got the following information for device %d\n", dev);

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
          *
          memcpy( (char*) &( sa.sin_addr ) , (char*)hostinfo->h_addr , hostinfo->h_length );
          */
         tmp = (char*) &(sa.sin_addr);
         for (i=0 ; i<hostinfo->h_length ; i++)
         {
            tmp[i] = hostinfo->h_addr[i];
         }

         __PO_HI_SET_SOCKET_TIMEOUT(nodes[dev].socket,100000);

         /*
          * We try to connect on the remote host. We try every
          * second to connect on.
          */

         ret = connect (nodes[dev].socket,
                        (struct sockaddr*) &sa ,
                        sizeof (struct sockaddr_in));

#ifdef __PO_HI_USE_PROTOCOL_MYPROTOCOL_I
         if (ret == 0)
         {
            __DEBUGMSG ("[DRIVER ETH] Connection established with device %d, socket=%d\n", dev, nodes[dev].socket);

            break;
         }
         else
         {
            __DEBUGMSG ("connect() failed, return=%d\n", ret);
         }

#else
         if (ret == 0)
         {

            __DEBUGMSG ("[DRIVER ETH] Send my id (%d) using socket %d (node %d)\n", id, nodes[dev].socket, dev);
            ret = write (nodes[dev].socket, &id, sizeof (__po_hi_device_id));
            if (ret != sizeof (__po_hi_device_id))
            {
               __DEBUGMSG ("[DRIVER ETH] Device %d cannot send his id (ret=%d)\n", id, ret);
            }
            __DEBUGMSG ("[DRIVER ETH] Connection established with device %d, socket=%d (ret=%d)\n", dev, nodes[dev].socket, ret);
            break;
         }
         else
         {
            __DEBUGMSG ("connect() failed, return=%d\n", ret);
         }
#endif

         if (close (nodes[dev].socket))
         {
            __DEBUGMSG ("[DRIVER ETH] Cannot close socket %d\n", nodes[dev].socket);
         }

         /*
          * We wait 500ms each time we try to connect on the
          * remote host
          */

         __po_hi_get_time (&current_time);
         __po_hi_milliseconds (&tmptime, 500);
         __po_hi_add_times (&mytime, &current_time, &tmptime);
         __DEBUGMSG ("[DRIVER ETH] Cannot connect on device %d, wait 500ms\n", dev);
         __po_hi_delay_until (&mytime);
      }
   }

   __DEBUGMSG ("[DRIVER ETH] INITIALIZATION DONE\n");

}
