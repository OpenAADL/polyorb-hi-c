/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2010-2014 ESA & ISAE.
 */


#include <deployment.h>
/* Generated code header */

#ifdef __PO_HI_NEED_DRIVER_1553_RASTA


#include <activity.h>
#include <marshallers.h>

#include <po_hi_debug.h>
#include <po_hi_transport.h>
#include <po_hi_gqueue.h>
#include <po_hi_messages.h>
#include <po_hi_utils.h>
#include <drivers/po_hi_rtems_utils.h>
#include <drivers/po_hi_driver_rasta_1553.h>
#include <drivers/po_hi_driver_rasta_1553_brmlib.h>

#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>
/* POSIX-style files */

#include <pci.h>
#include <rasta.h>
/* Rasta includes from GAISLER drivers */

#define __PO_HI_DRIVER_RASTA_1553_DEVICE "/dev/brmrasta0"

#define __PO_HI_NEED_DRIVER_1553_RASTA_MSG_CNT 4

__po_hi_c_driver_rasta_1553_brm_t         po_hi_c_driver_1553_rasta_fd;
__po_hi_request_t                         po_hi_c_driver_1553_rasta_request;
__po_hi_msg_t                             __po_hi_c_driver_1553_rasta_terminal_poller_msg;

void __po_hi_c_driver_1553_rasta_terminal_poller (void)
{
   int            ret;
   int            msglen;
   struct rt_msg  msgs[__PO_HI_NEED_DRIVER_1553_RASTA_MSG_CNT];

   __DEBUGMSG ("[RASTA 1553] Hello, i'm the poller !\n");

   __po_hi_c_driver_1553_rasta_brmlib_set_block(po_hi_c_driver_1553_rasta_fd,1,0);

   ret = __po_hi_c_driver_1553_rasta_brmlib_rt_recv (po_hi_c_driver_1553_rasta_fd,msgs);

   if ( ret <= 0 )
   {
      __DEBUGMSG ("[RASTA 1553] Error when receive, return code=%d\n",ret); 
      return;
   }

   __DEBUGMSG ("[RASTA 1553] Poller received %d messages\n",ret); 

   if ( msgs[0].desc >= 32 )
   {
      __DEBUGMSG ("[RASTA 1553] Received message desc >= 32\n");
      return;
   }

   __DEBUGMSG ("[RASTA 1553] ---------------  RT MESSAGE: -------------------\n");

   if (msgs[0].miw & (1<<7))
   {
      printf("[RASTA 1553] Message error, desc: %d, miw:%x\n", msgs[0].desc, msgs[0].miw);
   }

   __DEBUGMSG ("[RASTA 1553] desc: %d, miw: %x, time: %x\n",msgs[0].desc, msgs[0].miw, msgs[0].time);

   msglen = (msgs[0].miw >> 11) & 0x1f;

   memcpy (&__po_hi_c_driver_1553_rasta_terminal_poller_msg, msgs[0].data, __PO_HI_MESSAGES_MAX_SIZE);
   {
#include <stdio.h>
   printf("received (length=%d): 0x", msglen);
   int i;
   uint32_t* toto = (uint32_t*) &__po_hi_c_driver_1553_rasta_terminal_poller_msg;
   for (i = 0 ; i < __PO_HI_MESSAGES_MAX_SIZE ; i++)
   {
      printf("%x", toto[i]);
   }

   printf("\n");
   }


   __po_hi_unmarshall_request (&po_hi_c_driver_1553_rasta_request, &__po_hi_c_driver_1553_rasta_terminal_poller_msg);

   __DEBUGMSG ("[RASTA 1553] Destination port: %d\n", po_hi_c_driver_1553_rasta_request.port);

   __po_hi_main_deliver (&po_hi_c_driver_1553_rasta_request);
}


__po_hi_msg_t __po_hi_c_driver_1553_rasta_sender_terminal_msg;
int __po_hi_c_driver_1553_rasta_sender_terminal (const __po_hi_task_id task_id, const __po_hi_port_t port)
{
   int ts;
   int ret;
   struct rt_msg msgs[__PO_HI_NEED_DRIVER_1553_RASTA_MSG_CNT];

   __po_hi_local_port_t local_port;
   __po_hi_request_t* request;
   __po_hi_port_t destination_port;


   local_port = __po_hi_get_local_port_from_global_port (port);

   request = __po_hi_gqueue_get_most_recent_value (task_id, local_port);

   destination_port     = __po_hi_gqueue_get_destination (task_id, local_port, 0);

   __po_hi_msg_reallocate (&__po_hi_c_driver_1553_rasta_sender_terminal_msg);

   request->port = destination_port;

   __po_hi_marshall_request (request, &__po_hi_c_driver_1553_rasta_sender_terminal_msg);

   memcpy (msgs[0].data, &__po_hi_c_driver_1553_rasta_sender_terminal_msg, __PO_HI_MESSAGES_MAX_SIZE);

   msgs[0].miw = 0;
   msgs[0].miw |= (__PO_HI_MESSAGES_MAX_SIZE / 8) << 11;
   msgs[0].desc = 2;

   __po_hi_c_driver_1553_rasta_brmlib_set_block (po_hi_c_driver_1553_rasta_fd, 1, 0);

   ret = __po_hi_c_driver_1553_rasta_brmlib_rt_send (po_hi_c_driver_1553_rasta_fd, msgs);
   if (ret != 1)
   {
      printf("[RASTA 1553] Error when sending data, return code=%d\n", ret);
      return;
   }

   __DEBUGMSG  ("[RASTA 1553] Message sent: 0x");

   for (ts = 0 ; ts < __PO_HI_MESSAGES_MAX_SIZE ; ts++)
   {
      __DEBUGMSG ("%x", __po_hi_c_driver_1553_rasta_sender_terminal_msg.content[ts]);
   }
   __DEBUGMSG ("\n");

   return 1;
}


__po_hi_msg_t __po_hi_c_driver_1553_rasta_sender_controller_msg;
int __po_hi_c_driver_1553_rasta_sender_controller (const __po_hi_task_id task_id, const __po_hi_port_t port)
{
   struct bc_msg msgs[2];

   msgs[0].rtaddr[0] = 2;
   msgs[0].subaddr[0] = 1;
   msgs[0].wc = __PO_HI_MESSAGES_MAX_SIZE / 8;
   msgs[0].ctrl = 0;
//   msgs[0].ctrl |= BC_TR;
   msgs[0].ctrl |= BC_BUSA;

   msgs[1].ctrl |= BC_EOL;   /* end of list */

   __po_hi_local_port_t local_port;
   __po_hi_request_t* request;
   __po_hi_port_t destination_port;


   local_port = __po_hi_get_local_port_from_global_port (port);

   request = __po_hi_gqueue_get_most_recent_value (task_id, local_port);

   destination_port     = __po_hi_gqueue_get_destination (task_id, local_port, 0);

   __po_hi_msg_reallocate (&__po_hi_c_driver_1553_rasta_sender_controller_msg);

   request->port = destination_port;

   __po_hi_marshall_request (request, &__po_hi_c_driver_1553_rasta_sender_controller_msg);

   memcpy (msgs[0].data, &__po_hi_c_driver_1553_rasta_sender_controller_msg, __PO_HI_MESSAGES_MAX_SIZE);

   /*
   {
#include <stdio.h>
   printf("sent : 0x");
   int i;
   uint32_t* toto = (uint32_t*) &msg;
   for (i = 0 ; i < __PO_HI_MESSAGES_MAX_SIZE ; i++)
   {
      printf("%x", toto[i]);
   }

   printf("\n");
   }
   */
   
   __po_hi_c_driver_1553_rasta_brmlib_set_block (po_hi_c_driver_1553_rasta_fd, 1, 0);

   if ( __po_hi_c_driver_1553_rasta_proccess_list(po_hi_c_driver_1553_rasta_fd,msgs,0) )
   {
      __DEBUGMSG("[RASTA 1553] CANNOT PROCESS LIST\n");
      return 0;
   }

   return 1;
}



int __po_hi_c_driver_1553_rasta_proccess_list (__po_hi_c_driver_rasta_1553_brm_t chan, struct bc_msg *list, int test)
{
   int j,ret;

   if ( __po_hi_c_driver_1553_rasta_brmlib_bc_dolist(chan, list) )
   {
      __DEBUGMSG("[RASTA 1553] LIST EXECUTION INIT FAILED\n");
      return -1;
   }

   /* Blocks until done */
   __DEBUGMSG("[RASTA 1553] Waiting until list processed\n"); 
   if ( (ret=__po_hi_c_driver_1553_rasta_brmlib_bc_dolist_wait(chan)) < 0 )
   {
      __DEBUGMSG("[RASTA 1553] LIST EXECUTION DONE FAILED\n");
      return -1;
   }

   if ( ret != 1 ) 
   {
      /* not done */
      __DEBUGMSG("[RASTA 1553] LIST NOT PROCESSED\n");
      return -1;
   }

   /* done */
   __DEBUGMSG("[RASTA 1553] List processed.\n");

   for (j = 1; j <= __PO_HI_NEED_DRIVER_1553_RASTA_MSG_CNT; j++) 
   {
      if (list[j-1].ctrl & BC_BAME)
      {
         __DEBUGMSG("[RASTA 1553] Error msg %d, %x: BAME\n", j, list[j-1].ctrl);
      }
   }

   return 0;
}

void __po_hi_c_driver_1553_rasta_controller ()
{
   struct bc_msg cmd_list[__PO_HI_NEED_DRIVER_1553_RASTA_MSG_CNT+1];
   struct bc_msg result_list[__PO_HI_NEED_DRIVER_1553_RASTA_MSG_CNT+1];
   int j,k;

   __DEBUGMSG("[RASTA 1553] Starting task 1: BC mode\n");

   /* before starting set up
    *  ¤ blocking mode
    *  ¤ BC mode
    */


   /* total blocking mode */
   __DEBUGMSG("[RASTA 1553] Task1: Setting TX/RX blocking mode\n"); 
   __po_hi_c_driver_1553_rasta_brmlib_set_block(po_hi_c_driver_1553_rasta_fd,1,1);

   __DEBUGMSG("[RASTA 1553] Setting up command list.\n");


   /* Set up messages to RT receive subaddresses */
   for (j = 1; j <= __PO_HI_NEED_DRIVER_1553_RASTA_MSG_CNT; j++) 
   {
      cmd_list[j-1].rtaddr[0]  = 1;
      cmd_list[j-1].subaddr[0] = j;
      cmd_list[j-1].wc         = 8;
      cmd_list[j-1].ctrl       = BC_BUSA; /* RT receive on bus a */

      for (k = 0; k < 9; k++)
      {
         cmd_list[j-1].data[k] = 0;
      }

      /* message input */
      cmd_list[j-1].data[1] = 'G';
      cmd_list[j-1].data[2] = 'R';
      cmd_list[j-1].data[3] = (j-1)+7;
   }

   cmd_list[__PO_HI_NEED_DRIVER_1553_RASTA_MSG_CNT-1].wc++;
   cmd_list[__PO_HI_NEED_DRIVER_1553_RASTA_MSG_CNT].ctrl |= BC_EOL;   /* end of list */

   /* Set up RT transmit sub addresses (request RTs to send answer) */
   for (j = 1; j <= __PO_HI_NEED_DRIVER_1553_RASTA_MSG_CNT; j++) 
   {
      result_list[j-1].rtaddr[0]  = 1;
      result_list[j-1].subaddr[0] = j;
      result_list[j-1].wc         = 8;
      result_list[j-1].ctrl       = BC_BUSA | BC_TR; /* RT transmit on bus a */		
      /* clear data */
      for (k = 0; k < 9; k++)
      {
         result_list[j-1].data[k] = 0;
      }
   }

   result_list[__PO_HI_NEED_DRIVER_1553_RASTA_MSG_CNT-1].wc++;
   result_list[__PO_HI_NEED_DRIVER_1553_RASTA_MSG_CNT].ctrl |= BC_EOL;   /* end of list */

//   __DEBUGMSG("[RASTA 1553] -------------  BC: START LIST EXECUTION -------------\n");

//   __DEBUGMSG("[RASTA 1553] Start CMD list processing.\n"); 
   if ( __po_hi_c_driver_1553_rasta_proccess_list(po_hi_c_driver_1553_rasta_fd,cmd_list,0) )
   {
      return;
   }

   __DEBUGMSG("[RASTA 1553] -------------  BC: START LIST EXECUTION -------------\n");
   __DEBUGMSG("[RASTA 1553] Start RESULT list processing.\n"); 

   /* Clear data that input will overwrite */
   for (j = 1; j <= __PO_HI_NEED_DRIVER_1553_RASTA_MSG_CNT; j++) 
   {
      /* clear data */
      for (k = 0; k < 8; k++)
      {
         result_list[j-1].data[k] = 0;
      }
   }

   if ( __po_hi_c_driver_1553_rasta_proccess_list(po_hi_c_driver_1553_rasta_fd,result_list,1) )
   {
      return;
   }

   /* print the data that was received */
   /*
   j=1;
   while( !(result_list[j-1].ctrl & BC_EOL) )
   {
      __DEBUGMSG("[RASTA 1553] Response to message %d: (len: %d, tsw1: %x, tsw2: %x)\n  ",j,result_list[j-1].wc,result_list[j-1].tsw[0],result_list[j-1].tsw[1]);
     for (k = 0; k < result_list[j-1].wc; k++)
      {
         if ( isalnum(result_list[j-1].data[k]) )
         {
            __DEBUGMSG("[RASTA 1553] 0x%x (%c)",result_list[j-1].data[k],result_list[j-1].data[k]);
         }
         else
         {
            __DEBUGMSG("[RASTA 1553] 0x%x (.)",result_list[j-1].data[k]);
         }
      }
      __DEBUGMSG("\n");
      
      j++;
   }
   */

}



void __po_hi_c_driver_1553_rasta_init_terminal (__po_hi_device_id id)
{
   int ret;

   __DEBUGMSG ("[RASTA 1553] Init\n");
   init_pci();
   __DEBUGMSG ("[RASTA 1553] Initializing RASTA (rasta_register()) ...\n");
   if (rasta_register())
   {
      __DEBUGMSG(" ERROR !\n");
      return;
   }

   __DEBUGMSG(" OK !\n");

   po_hi_c_driver_1553_rasta_fd = __po_hi_c_driver_1553_rasta_brmlib_open (__PO_HI_DRIVER_RASTA_1553_DEVICE);

   if (po_hi_c_driver_1553_rasta_fd < 0)
   {
      __DEBUGMSG ("[RASTA 1553] Unable to open 1553 device\n");
      return;
   }

   ret = __po_hi_c_driver_1553_rasta_brmlib_set_mode (po_hi_c_driver_1553_rasta_fd,BRM_MODE_RT);

   if (ret != 0)
   {
      __DEBUGMSG ("Error setting address, return=%d\n", ret);
      return;
   }

   ret = __po_hi_c_driver_1553_rasta_brmlib_set_rt_addr (po_hi_c_driver_1553_rasta_fd, 2);

   if (ret != 0)
   {
      __DEBUGMSG ("Error setting address, return=%d\n", ret);
      return;
   }
   return;
}


void __po_hi_c_driver_1553_rasta_init_controller (__po_hi_device_id id)
{
   int ret;

   __DEBUGMSG ("[RASTA 1553] Init\n");
   init_pci();
   __DEBUGMSG ("[RASTA 1553] Initializing RASTA (rasta_register()) ...\n");
   if (rasta_register())
   {
      __DEBUGMSG(" ERROR !\n");
      return;
   }

   __DEBUGMSG(" OK !\n");

   po_hi_c_driver_1553_rasta_fd = __po_hi_c_driver_1553_rasta_brmlib_open (__PO_HI_DRIVER_RASTA_1553_DEVICE);

   if (po_hi_c_driver_1553_rasta_fd < 0)
   {
      __DEBUGMSG ("[RASTA 1553] Unable to open 1553 device\n");
      return;
   }

   /* Set BC mode */
   __DEBUGMSG("[RASTA 1553] Setting BC mode\n");

   ret = __po_hi_c_driver_1553_rasta_brmlib_set_mode (po_hi_c_driver_1553_rasta_fd,BRM_MODE_BC);

   if (ret != 0)
   {
      __DEBUGMSG ("Error setting BC mode, return=%d\n", ret);
   }

}



#endif
