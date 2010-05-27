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

#if (defined (__PO_HI_NEED_DRIVER_SOCKETS) || defined (__PO_HI_NEED_DRIVER_SOCKETS_ASN1))

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


#include <po_hi_debug.h>
#include <po_hi_common.h>
#include <po_hi_time.h>
#include <po_hi_task.h>
#include <drivers/po_hi_driver_sockets_asn1.h>
#include <drivers/po_hi_driver_sockets_common.h>
#include <drivers/po_hi_driver_sockets.h>

__po_hi_inetnode_t nodes[__PO_HI_NB_NODES];
__po_hi_inetnode_t rnodes[__PO_HI_NB_NODES];

void __po_hi_driver_sockets_init (__po_hi_device_id id)
{
   int                i;
   int                ret;
   int                reuse;
   char               *tmp;
   __po_hi_uint16_t   node;
   __po_hi_time_t     mytime;
   struct sockaddr_in sa;
   struct hostent*    hostinfo;

   /* Initialization of all sockets */

   for (node = 0 ; node < __PO_HI_NB_NODES ; node++)
   {
      nodes[node].socket = -1;
   }


   /*
    * If the current node port has a port number, then it has to
    * listen to other nodes. So, we create a socket, bind it and
    * listen to other nodes.
    */
   if ( node_port[mynode] != __PO_HI_NOPORT )
   {
      nodes[mynode].socket = socket (AF_INET, SOCK_STREAM, 0);

      if (nodes[mynode].socket == -1 )
      {
#ifdef __PO_HI_DEBUG
         __DEBUGMSG ("Cannot create socket for node %d\n", mynode);
#endif
         return;
      }

      reuse = 1;
      setsockopt (nodes[mynode].socket, SOL_SOCKET, SO_REUSEADDR, &reuse, sizeof (reuse));

      sa.sin_addr.s_addr = htonl (INADDR_ANY);   /* We listen on all adresses */
      sa.sin_family = AF_INET;                   
      sa.sin_port = htons (node_port[mynode]);   /* Port provided by the generated code */

      if( bind( nodes[mynode].socket , ( struct sockaddr * ) &sa , sizeof( struct sockaddr_in ) ) < 0 )
      {
#ifdef __PO_HI_DEBUG
         __DEBUGMSG ("Unable to bind socket and port on socket %d\n", nodes[mynode].socket);
#endif
      }

      if( listen( nodes[mynode].socket , __PO_HI_NB_ENTITIES ) < 0 )
      {
#ifdef __PO_HI_DEBUG
         __DEBUGMSG ("Cannot listen on socket %d\n", nodes[mynode].socket);
#endif
      }

      /* 
       * Create the thread which receive all data from other
       * nodes. This thread will execute the function
       * __po_hi_receiver_task
       */

      __po_hi_initialize_add_task ();

#ifdef __PO_HI_NEED_DRIVER_SOCKETS
      __po_hi_create_generic_task 
         (-1, 0,__PO_HI_MAX_PRIORITY, 0, __po_hi_sockets_receiver_task);
#endif

#ifdef __PO_HI_NEED_DRIVER_SOCKETS_ASN1
      __po_hi_create_generic_task 
         (-1, 0,__PO_HI_MAX_PRIORITY, 0, __po_hi_sockets_asn1_poller);
#endif

   }

   /*
    * For each node in the sytem that may communicate with the current
    * node we create a socket. This socket will be used to send data.
    */
   for (node = 0 ; node < __PO_HI_NB_NODES ; node++ )
   {
      if ( (node != mynode) && (node_port[node] != __PO_HI_NOPORT) && (nodes[node].socket == -1) )
      {
         while (1)
         {
            nodes[node].socket = socket (AF_INET, SOCK_STREAM, 0);

            if (nodes[node].socket == -1 )
            {
#ifdef __PO_HI_DEBUG
               __DEBUGMSG ("Socket for node %d is not created", node);
#endif
               return;
            }

            hostinfo = gethostbyname ((char*)node_addr[node]);

            if (hostinfo == NULL )
            {
#ifdef __PO_HI_DEBUG
               __DEBUGMSG ("Error while getting host informations for node %d\n", node);
#endif
            }

            sa.sin_port = htons( node_port[node] );
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
             */

            ret = connect 
               (nodes[node].socket, ( struct sockaddr* ) &sa , sizeof( struct sockaddr_in ));

            if (ret == 0)
            {
               if (write (nodes[node].socket, &mynode, sizeof (__po_hi_node_t)) != sizeof (__po_hi_node_t))
               {
#ifdef __PO_HI_DEBUG
                  __DEBUGMSG ("Node %d cannot send his node-id\n", node);
#endif
               }
               break;
            }

            if (close (nodes[node].socket))
            {
#ifdef __PO_HI_DEBUG
               __DEBUGMSG ("Cannot close socket %d\n", nodes[node].socket);
#endif
            }

            /*
             * We wait 500ms each time we try to connect on the
             * remote host
             */

            __po_hi_get_time (&mytime);
            __po_hi_delay_until (__po_hi_add_times (mytime, __po_hi_milliseconds (500)));
         }
      }
   }
}

#endif /* __PO_HI_NEED_DRIVER_SOCKETS || __PO_HI_NEED_DRIVER_SOCKETS_ASN1 */
