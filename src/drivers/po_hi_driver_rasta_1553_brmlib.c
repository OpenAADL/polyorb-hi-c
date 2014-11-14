/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2010-2014 ESA & ISAE.
 */

/*
 * This code has been greatly inspired by GAISLER examples.
 */

#include <deployment.h>
/* Generated code header */

#ifdef __PO_HI_NEED_DRIVER_1553_RASTA

#include <rtems.h>
#include <stdlib.h>
#include <errno.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#include <b1553brm.h>
#include <po_hi_debug.h>
#include <drivers/po_hi_driver_rasta_1553_brmlib.h>

/* The stupid rtems name to errno table, in fact I hate it.... :)
 *
rtems_assoc_t errno_assoc[] = {
    { "OK",                 RTEMS_SUCCESSFUL,                0 },
    { "BUSY",               RTEMS_RESOURCE_IN_USE,           EBUSY },
    { "INVALID NAME",       RTEMS_INVALID_NAME,              EINVAL },
    { "NOT IMPLEMENTED",    RTEMS_NOT_IMPLEMENTED,           ENOSYS },
    { "TIMEOUT",            RTEMS_TIMEOUT,                   ETIMEDOUT },
    { "NO MEMORY",          RTEMS_NO_MEMORY,                 ENOMEM },
    { "NO DEVICE",          RTEMS_UNSATISFIED,               ENODEV },
    { "INVALID NUMBER",     RTEMS_INVALID_NUMBER,            EBADF},
    { "NOT RESOURCE OWNER", RTEMS_NOT_OWNER_OF_RESOURCE,     EPERM},
    { "IO ERROR",           RTEMS_IO_ERROR,                  EIO},
    { 0, 0, 0 },
};
*/

__po_hi_c_driver_rasta_1553_brm_t __po_hi_c_driver_1553_rasta_brmlib_open(char *driver_name)
{
	int fd;
	__po_hi_c_driver_rasta_1553_brm_t ret = NULL;
	
	__DEBUGMSG("[RASTA 1553 BRMLIB] Opening driver %s ...",driver_name);
	
	fd = open(driver_name,O_RDWR);
	if ( fd >= 0 )
   {
		ret = calloc(sizeof(*ret),1);
		ret->fd = fd;
		/* Initial state of driver */
		ret->mode = BRM_MODE_RT;
	   __DEBUGMSG("OK !\n");
	
	}
   else
   {
		if ( errno == ENODEV )
      {
			__DEBUGMSG(" driver %s doesn't exist\n",driver_name);
		}
      else
      {
         if ( errno == EBUSY )
         {
			   __DEBUGMSG(" channel already taken\n");
		   }
         else
         {
			   __DEBUGMSG(" unknown error, errno: %d, ret: %d\n",errno,fd);
         }
		}
	}
	
	return ret;
}

void __po_hi_c_driver_1553_rasta_brmlib_close(__po_hi_c_driver_rasta_1553_brm_t chan){
	if ( !chan || (chan->fd<0) )
   {
		return;
   }
	close(chan->fd);
	free(chan);
}

int __po_hi_c_driver_1553_rasta_brmlib_rt_send_multiple(__po_hi_c_driver_rasta_1553_brm_t chan, struct rt_msg *msgs, int msgcnt)
{

	int ret;

	if ( !chan || !msgs || (msgcnt < 0) )
   {
		return -1;
   }
	
	if ( msgcnt == 0 )
   {
		return 0;
   }
	
	ret = write(chan->fd,msgs,msgcnt);

	if ( ret < 0 )
   {
		/* something went wrong 
		 * OR in non-blocking mode
		 * that would block
		 */
		if ( !chan->txblk && (errno == EBUSY) )
      {
			/* would block ==> 0 sent is ok */
			return 0;
		}
			
		if ( errno == EINVAL )
      {
			/* CAN must be started before receiving */
			__DEBUGMSG("[RASTA 1553 BRMLIB] input descriptor numbering error\n");
			return -1;
		}

		__DEBUGMSG("[RASTA 1553 BRMLIB] error in write, errno: %d, returned: %d\n",errno,ret);
		return -1;
	}
	
	/* sent all of them */
	return ret;
}

int __po_hi_c_driver_1553_rasta_brmlib_rt_send(__po_hi_c_driver_rasta_1553_brm_t chan, struct rt_msg *msg)
{
   return __po_hi_c_driver_1553_rasta_brmlib_rt_send_multiple(chan,msg,1);
}

int __po_hi_c_driver_1553_rasta_brmlib_recv_multiple(__po_hi_c_driver_rasta_1553_brm_t chan, void *msgs, int msglen)
{
	int ret;
	
	if ( !chan || !msgs || (msglen<0) )
   {
		return -1;
   }
	
	if ( msglen == 0 )
   {
		__DEBUGMSG("[RASTA 1553 BRMLIB] zero length, errno: %d, returned: %d\n",errno,ret);
		return 0;
   }
	
	errno = 0;

	ret = read(chan->fd,msgs,msglen);

	if ( ret < 0 )
   {
		/* something went wrong 
		 * OR in non-blocking mode
		 * that would block
		 */
		if ( !chan->rxblk && (errno == EBUSY) )
      {
			return 0;
		}
		
		__DEBUGMSG("[RASTA 1553 BRMLIB] error in read, errno: %d, returned: %d\n",errno,ret);
		return -1;
	}
	
	/* message count is returned, not byte count */
	return ret;
}

int __po_hi_c_driver_1553_rasta_brmlib_rt_recv_multiple(__po_hi_c_driver_rasta_1553_brm_t chan, struct rt_msg *msgs, int msgcnt)
{
	if ( !chan || (chan->mode!=BRM_MODE_RT) )
   {
		return -1;
   }
	
	/* Read the messages */
	return __po_hi_c_driver_1553_rasta_brmlib_recv_multiple(chan,(void *)msgs,msgcnt);
}

int __po_hi_c_driver_1553_rasta_brmlib_bm_recv_multiple(__po_hi_c_driver_rasta_1553_brm_t chan, struct bm_msg *msgs, int msgcnt)
{
	if ( !chan || (chan->mode!=BRM_MODE_BM) )
   {
		return -1;
   }
	
	/* Read the messages */
	return __po_hi_c_driver_1553_rasta_brmlib_recv_multiple(chan,(void *)msgs,msgcnt);
}

int __po_hi_c_driver_1553_rasta_brmlib_rt_recv(__po_hi_c_driver_rasta_1553_brm_t chan, struct rt_msg *msg)
{
	return __po_hi_c_driver_1553_rasta_brmlib_rt_recv_multiple(chan,msg,1);
}


int __po_hi_c_driver_1553_rasta_brmlib_bm_recv(__po_hi_c_driver_rasta_1553_brm_t chan, struct bm_msg *msg)
{
	return __po_hi_c_driver_1553_rasta_brmlib_bm_recv_multiple(chan,msg,1);
}


int __po_hi_c_driver_1553_rasta_brmlib_set_mode(__po_hi_c_driver_rasta_1553_brm_t chan, unsigned int mode)
{
	int ret;
	unsigned int arg = mode;
	
	if ( !chan )
   {
		return -1;
   }
	
	ret = ioctl(chan->fd,BRM_SET_MODE,&arg);

	if ( ret < 0 )
   {
		if ( errno == EINVAL )
      {
			__DEBUGMSG("[RASTA 1553 BRMLIB] set_mode invalid mode: %d\n",arg);
			return -2;
		}
	
		if ( errno == ENOMEM )
      {
			/* started */
			__DEBUGMSG("[RASTA 1553 BRMLIB] set_mode: not enough memory\n");
			return -3;
		}
		
		/* unhandeled errors */
		__DEBUGMSG("[RASTA 1553 BRMLIB] set_mode: failed, errno: %d, ret: %d\n",errno,ret);
		return -1;
	}
	
	/* Save mode */
	chan->mode = mode;
	
	return 0;
}

int __po_hi_c_driver_1553_rasta_brmlib_set_bus(__po_hi_c_driver_rasta_1553_brm_t chan, unsigned int bus)
{
	int ret;
	unsigned int arg = bus;
	if ( !chan )
   {
		return -1;
   }
		
	/* only for RT mode */
	if ( chan->mode != BRM_MODE_RT )
   {
		__DEBUGMSG("[RASTA 1553 BRMLIB] set_bus: Only possible to set bus in RT mode\n");
		return -2; /* fast EINVAL... */
	}
	
	ret = ioctl(chan->fd,BRM_SET_BUS,&arg);

	if ( ret < 0 )
   {
		if ( errno == EINVAL )
      {
			__DEBUGMSG("[RASTA 1553 BRMLIB] set_bus: invalid bus: %d\n",arg);
			return -2;
		}
		
		/* unhandeled errors */
		__DEBUGMSG("[RASTA 1553 BRMLIB] set_bus: failed, errno: %d, ret: %d\n",errno,ret);
		return -1;
	}
	return 0;
}

int __po_hi_c_driver_1553_rasta_brmlib_set_msg_timeout(__po_hi_c_driver_rasta_1553_brm_t chan, unsigned int timeout)
{
	int ret;
	unsigned int arg = timeout;
	
	if ( !chan )
   {
		return -1;
   }
	
	if ( !((chan->mode==BRM_MODE_BM) || (chan->mode==BRM_MODE_BC)) )
   {
		__DEBUGMSG("[RASTA 1553 BRMLIB] set_msg_timeout: Only possible to set bus in BC & BM mode\n");
		return -2;
	}
	
	ret = ioctl(chan->fd,BRM_SET_MSGTO,&arg);

	if ( ret < 0 )
   {
		if ( errno == EBUSY )
      {
			/* started */
			__DEBUGMSG("[RASTA 1553 BRMLIB] set_msg_timeout: started\n");
			return -2;
		}
		
		__DEBUGMSG("[RASTA 1553 BRMLIB] set_msg_timeout: failed, errno: %d, ret: %d\n",errno,ret);
		return -1;
	}
	
	return 0;
}

int __po_hi_c_driver_1553_rasta_brmlib_set_rt_addr(__po_hi_c_driver_rasta_1553_brm_t chan, unsigned int address)
{
	int ret;
	unsigned int arg = address;
	
	if ( !chan )
   {
		return -1;
   }
	
	if ( chan->mode != BRM_MODE_RT )
   {
		__DEBUGMSG("[RASTA 1553 BRMLIB] set_rt_addr: not in RT mode\n");
		return -2;
	}
	
	ret = ioctl(chan->fd,BRM_SET_RT_ADDR,&arg);

	if ( ret < 0 )
   {
		__DEBUGMSG("[RASTA 1553 BRMLIB] set_rt_addr: failed, errno: %d, ret: %d\n",errno,ret);
		return -1;
	}
	
	return 0;
}

int __po_hi_c_driver_1553_rasta_brmlib_set_std(__po_hi_c_driver_rasta_1553_brm_t chan, int std){
	int ret;
	unsigned int arg = std;
	
	if ( !chan )
   {
		return -1;
   }
	
	ret = ioctl(chan->fd,BRM_SET_STD,&arg);

	if ( ret < 0 )
   {
		if ( errno == EINVAL )
      {
			/* started */
			__DEBUGMSG("[RASTA 1553 BRMLIB] set_std: new standard not valid: %d\n",arg);
			return -2;
		}
		
		__DEBUGMSG("[RASTA 1553 BRMLIB] set_filter: failed, errno: %d, ret: %d\n",errno,ret);
		return -1;
	}
	
	return 0;
}


int __po_hi_c_driver_1553_rasta_brmlib_set_txblock(__po_hi_c_driver_rasta_1553_brm_t chan, int txblocking)
{
	unsigned int arg = (txblocking) ? 1 : 0;
	int ret;
	
	if ( !chan )
   {
		return -1;
   }
	
	ret = ioctl(chan->fd,BRM_TX_BLOCK,&arg);

	if ( ret < 0 )
   {
		__DEBUGMSG("[RASTA 1553 BRMLIB] set_txblock: failed, errno: %d, ret: %d\n",errno,ret);
		return -1;
	}

	/* remember blocking state */
	chan->txblk = arg;
	return 0;
}


int __po_hi_c_driver_1553_rasta_brmlib_set_rxblock(__po_hi_c_driver_rasta_1553_brm_t chan, int rxblocking){
	unsigned int arg = (rxblocking) ? 1 : 0;
	int ret;
	
	if ( !chan )
   {
		return -1;
   }
	
	ret = ioctl(chan->fd,BRM_RX_BLOCK,&arg);

	if ( ret < 0 )
   {
		__DEBUGMSG("[RASTA 1553 BRMLIB] set_rxblock: failed, errno: %d, ret: %d\n",errno,ret);
		return -1;
	}

	/* remember blocking state */
	chan->rxblk = arg;

	return 0;
}

int __po_hi_c_driver_1553_rasta_brmlib_set_block(__po_hi_c_driver_rasta_1553_brm_t chan, int txblocking, int rxblocking){
	int ret;

	ret = __po_hi_c_driver_1553_rasta_brmlib_set_txblock(chan,txblocking);

	if ( !ret )
   {
		return __po_hi_c_driver_1553_rasta_brmlib_set_rxblock(chan,rxblocking);
	}

	return ret;
}

int __po_hi_c_driver_1553_rasta_brmlib_set_broadcast(__po_hi_c_driver_rasta_1553_brm_t chan, int broadcast){
	unsigned int arg = (broadcast) ? 1 : 0;
	int ret;
	
	if ( !chan )
   {
		return -1;
   }
	
	ret = ioctl(chan->fd,BRM_SET_BCE,&arg);

	if ( ret < 0 )
   {
		__DEBUGMSG("[RASTA 1553 BRMLIB] set_broadcast: failed, errno: %d, ret: %d\n",errno,ret);
		return -1;
	}
	
	/* remember broadcast state */
	chan->broadcast = arg;
	return 0;
}

int __po_hi_c_driver_1553_rasta_brmlib_bc_dolist(__po_hi_c_driver_rasta_1553_brm_t chan, struct bc_msg *msgs)
{
	int ret;
	
	ret = ioctl(chan->fd, BRM_DO_LIST, msgs);

	if ( ret < 0 )
   {
		if ( errno == EINVAL )
      {
			__DEBUGMSG("[RASTA 1553 BRMLIB] bc_dolist: not in BC mode\n");
			return -2;
		}

		if ( errno == EBUSY )
      {
			__DEBUGMSG("[RASTA 1553 BRMLIB] bc_dolist: busy\n");
			return -3;
		}
		
		__DEBUGMSG("[RASTA 1553 BRMLIB] dolist: errno %d, ret: %d\n",errno,ret);
		return -1;
	}
	return 0;
}

int __po_hi_c_driver_1553_rasta_brmlib_bc_dolist_wait(__po_hi_c_driver_rasta_1553_brm_t chan)
{
	int ret;
	unsigned int result;
	
	ret = ioctl(chan->fd, BRM_LIST_DONE, &result);

	if ( ret < 0 )
   {
		if ( errno == EINVAL )
      {
			__DEBUGMSG("[RASTA 1553 BRMLIB] bc_dolist: not in BC mode\n");
			return -2;
		}

		if ( errno == EBUSY )
      {
			__DEBUGMSG("[RASTA 1553 BRMLIB] dolist: busy\n");
			return -3;
		}
		
		__DEBUGMSG("[RASTA 1553 BRMLIB] bc_dolist: errno %d, ret: %d\n",errno,ret);
		return -1;
	}
	
	return result;
}

void __po_hi_c_driver_rasta_1553_print_rt_msg(int i, struct rt_msg *msg)
{
	int k, wc;

	wc = msg->miw >> 11;

	__DEBUGMSG("[RASTA 1553 BRMLIB] MSG[%d]: miw: 0x%x, time: 0x%x, desc: 0x%x, len: %d\n  ",i,msg->miw,msg->time,msg->desc,wc);

	/* print data */			
	for (k = 0; k < wc; k++)
   {
		if ( isalnum(msg->data[k]) )
      {
         __DEBUGMSG("0x%x (%c)",msg->data[k],msg->data[k]);
		}
      else
      {
			__DEBUGMSG("0x%x (.)",msg->data[k]);
		}
	}
	if ( k > 0 )
   {
		__DEBUGMSG("\n");
   }
}

void __po_hi_c_driver_rasta_1553_print_bm_msg(int i, struct bm_msg *msg)
{
	int k,wc,tr,desc;

	wc = msg->cw1 & 0x1f;	

	desc = (msg->cw1 >> 5) & 0x1f;

	tr = msg->cw1 & 0x0400;

	__DEBUGMSG("[RASTA 1553 BRMLIB] MSG[%d]: miw: 0x%x, cw1: 0x%x, cw2: 0x%x, desc: %d\n",i,msg->miw,msg->cw1,msg->cw2,desc);

	__DEBUGMSG("         sw1: 0x%x, sw2: 0x%x, tim: 0x%x, len: %d\n",msg->sw1,msg->sw2,msg->time,wc);
	
	/* no message data in BC transmit commands */
	if ( tr )
   {
		return;
   }
	
	__DEBUGMSG("         ");
	
	/* print data */			
	for (k = 0; k<wc; k++)
   {
		if ( isalnum(msg->data[k]) )
      {
         __DEBUGMSG("0x%x (%c)",msg->data[k],msg->data[k]);
		}
      else
      {
			__DEBUGMSG("0x%x (.)",msg->data[k]);
		}
	}

	if ( k > 0 )
   {
		__DEBUGMSG("\n");
   }
}

#endif
