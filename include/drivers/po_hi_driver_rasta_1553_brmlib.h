/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2012-2014 ESA & ISAE.
 */

#ifndef __PO_HI_DRIVER_RASTA_1553_BRM_LIB_H__
#define __PO_HI_DRIVER_RASTA_1553_BRM_LIB_H__

#include <deployment.h>
/* Generated code header */

#ifdef __PO_HI_NEED_DRIVER_1553_RASTA

/*
 * This code has been greatly inspired by GAISLER examples.
 */

#include <bsp.h>
#include <rtems/libio.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <sched.h>
#include <ctype.h>
#include <rtems/bspIo.h>
#include <b1553brm.h>

typedef struct {
	int fd;
	int mode; /* defaults to RT */
	int txblk;
	int rxblk;
	int broadcast;
} __po_hi_c_driver_rasta_1553_brm_s;

typedef __po_hi_c_driver_rasta_1553_brm_s *__po_hi_c_driver_rasta_1553_brm_t;

/* 
 * return file descriptor 
 */
__po_hi_c_driver_rasta_1553_brm_t __po_hi_c_driver_1553_rasta_brmlib_open(char *driver_name);

void __po_hi_c_driver_1553_rasta_brmlib_close(__po_hi_c_driver_rasta_1553_brm_t chan);


int __po_hi_c_driver_1553_rasta_brmlib_rt_send_multiple(__po_hi_c_driver_rasta_1553_brm_t chan, struct rt_msg *msgs, int msgcnt);

int __po_hi_c_driver_1553_rasta_brmlib_rt_send(__po_hi_c_driver_rasta_1553_brm_t chan, struct rt_msg *msg);

int __po_hi_c_driver_1553_rasta_brmlib_rt_recv_multiple(__po_hi_c_driver_rasta_1553_brm_t chan, struct rt_msg *msgs, int msgcnt);

int __po_hi_c_driver_1553_rasta_brmlib_rt_recv(__po_hi_c_driver_rasta_1553_brm_t chan, struct rt_msg *msg);

int __po_hi_c_driver_1553_rasta_brmlib_bm_recv_multiple(__po_hi_c_driver_rasta_1553_brm_t chan, struct bm_msg *msgs, int msgcnt);

int __po_hi_c_driver_1553_rasta_brmlib_bm_recv(__po_hi_c_driver_rasta_1553_brm_t chan, struct bm_msg *msg);

/* start execute a command list */
int __po_hi_c_driver_1553_rasta_brmlib_bc_dolist(__po_hi_c_driver_rasta_1553_brm_t chan, struct bc_msg *msgs);

/* wait for command list the finish the execution */
int __po_hi_c_driver_1553_rasta_brmlib_bc_dolist_wait(__po_hi_c_driver_rasta_1553_brm_t chan);


/* mode = 0,1,2
 * 0 = BC
 * 1 = RT
 * 2 = BM
 */
int __po_hi_c_driver_1553_rasta_brmlib_set_mode(__po_hi_c_driver_rasta_1553_brm_t chan, unsigned int mode);

/* bus=0,1,2,3
 * 0 = none
 * 1 = bus A
 * 2 = bus B
 * 3 = bus A and B 
 */
int __po_hi_c_driver_1553_rasta_brmlib_set_bus (__po_hi_c_driver_rasta_1553_brm_t chan, unsigned int bus);

int __po_hi_c_driver_1553_rasta_brmlib_set_txblock (__po_hi_c_driver_rasta_1553_brm_t chan, int txblocking);
int __po_hi_c_driver_1553_rasta_brmlib_set_rxblock (__po_hi_c_driver_rasta_1553_brm_t chan, int rxblocking);
int __po_hi_c_driver_1553_rasta_brmlib_set_block (__po_hi_c_driver_rasta_1553_brm_t chan, int txblocking, int rxblocking);
int __po_hi_c_driver_1553_rasta_brmlib_set_broadcast (__po_hi_c_driver_rasta_1553_brm_t chan, int broadcast);
int __po_hi_c_driver_1553_rasta_brmlib_set_std (__po_hi_c_driver_rasta_1553_brm_t chan, int std);
int __po_hi_c_driver_1553_rasta_brmlib_set_rt_addr (__po_hi_c_driver_rasta_1553_brm_t chan, unsigned int address);
int __po_hi_c_driver_1553_rasta_brmlib_set_msg_timeout (__po_hi_c_driver_rasta_1553_brm_t chan, unsigned int timeout);

/* DEBUG FUNCTIONS */
void __po_hi_c_driver_rasta_1553_print_rt_msg (int i, struct rt_msg *msg);
void __po_hi_c_driver_rasta_1553_print_bm_msg (int i, struct bm_msg *msg);

#endif
#endif
