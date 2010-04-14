/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2008, GET-Telecom Paris.
 */

#include <po_hi_config.h>
#include <po_hi_task.h>
#include <po_hi_transport.h>
#include <po_hi_protocols.h>
#include <po_hi_debug.h>
#include <po_hi_types.h>
#include <po_hi_messages.h>
#include <po_hi_returns.h>
#include <po_hi_main.h>
#include <po_hi_task.h>

#ifdef __PO_HI_USE_GIOP
#include <po_hi_giop.h>
#endif

#include <deployment.h>
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
 * This file (po_hi_transport_sockets.c) provides function to handle
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
 * The following extern variables are declared in the generated code
 * See the files deployment.h and deployment.c.
 */

extern __po_hi_inetport_t node_port[__PO_HI_NB_NODES];
extern __po_hi_inetaddr_t node_addr[__PO_HI_NB_NODES];
extern __po_hi_node_t mynode;
extern __po_hi_node_t entity_table[__PO_HI_NB_ENTITIES];

/*
 * Add the definition of __po_hi_queue_put, defined in
 * po_hi_transport.c This function is not defined in the header file,
 * because we don't want to publish it to the developer
 */

int __po_hi_queue_put (__po_hi_queue_id queue_id,
		       __po_hi_msg_t*   msg);


void* __po_hi_receiver_task (void);

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

void __po_hi_initialize_transport_low_level ()
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

      __po_hi_create_generic_task 
	(-1, 0,__PO_HI_MAX_PRIORITY, 0, __po_hi_receiver_task);

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

int __po_hi_transport_low_level_send (__po_hi_entity_t from, 
				      __po_hi_entity_t to, 
				      __po_hi_msg_t* msg)
{
  __po_hi_node_t  node;
  int             len;
  int             size_to_write;
  int             optval = 0;
  socklen_t       optlen = 0;
  
  node = entity_table[to];
  
  if (nodes[node].socket == -1 )
    {
#ifdef __PO_HI_DEBUG
      __DEBUGMSG ("... failure ...\n");
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
      __DEBUGMSG ("Error %s, %d\n", __FILE__, __LINE__);
      close (nodes[node].socket);
      nodes[node].socket = -1;
      return __PO_HI_ERROR_TRANSPORT_SEND;		
   }

  if (optval != 0)
    {
      __DEBUGMSG ("Error %s, %d", __FILE__, __LINE__);
      close (nodes[node].socket);
      nodes[node].socket = -1;
      return __PO_HI_ERROR_TRANSPORT_SEND;		
    }
  
  /* Ignore SIGPIPE to be able to recover from errors instead of crashing the node */

  if (signal (SIGPIPE, SIG_IGN) == SIG_ERR)
    {
      __DEBUGMSG ("Error %s, %d", __FILE__, __LINE__);
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
      __DEBUGMSG ("Error %s, %d", __FILE__, __LINE__);
      close (nodes[node].socket);
      nodes[node].socket = -1;
      return __PO_HI_ERROR_TRANSPORT_SEND;		
    }

  __DEBUGMSG (" ... success ... \n");
  
  return __PO_HI_SUCCESS;
}


void* __po_hi_receiver_task (void)
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
		     __po_hi_main_deliver (&decoded_msg);
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
	     __po_hi_main_deliver (&msg);
#endif
	     __po_hi_msg_reallocate(&msg);        /* re-initialize the message */
	   }
       }
   }  
  return NULL;
}

int __po_hi_transport_need_receiver_task ()
{
   if ((__PO_HI_NB_NODES > 1) && (node_port[mynode] != __PO_HI_NOPORT))
   {
      return 1;
   }

   return 0;
}
