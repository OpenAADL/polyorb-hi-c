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

#ifndef __PO_HI_DRIVER_RASTA_1553_H__
#define __PO_HI_DRIVER_RASTA_1553_H__

#ifdef __PO_HI_NEED_DRIVER_1553_RASTA

#include <drivers/po_hi_driver_rasta_1553_brmlib.h>

void  __po_hi_c_driver_1553_rasta_terminal_poller (void);
/*
 * __po_hi_c_driver_1553_rasta_terminal_poller is the function that should
 * be executed on a receiver node to wait for incoming data and put in 
 * the middleware queue. It must be called by a periodic thread.
 */

void __po_hi_c_driver_1553_rasta_init_terminal (__po_hi_device_id id);
/*
 * __po_hi_c_driver_1553_rasta_init_terminal initializes the board
 * and sets it in the TERMINAL mode.
 */

void __po_hi_c_driver_1553_rasta_init_controller (__po_hi_device_id id);
/*
 * __po_hi_c_driver_1553_rasta_init_terminal initializes the board
 * and sets it in the CONTROLLER mode.
 */

int   __po_hi_c_driver_1553_rasta_sender_controller (const __po_hi_task_id task_id, const __po_hi_port_t port);
/*
 * This function is used on a CONTROLLER to send a message to another node. It
 * can't be used when the device is acting as a MONITOR or a TERMINAL.
 */

int   __po_hi_c_driver_1553_rasta_sender_terminal (const __po_hi_task_id task_id, const __po_hi_port_t port);
/*
 * This function is used on a TERMINAL to send a message to another node. It
 * can't be used when the device is acting as a MONITOR or a CONTROLLER;
 */

void  __po_hi_c_driver_1553_rasta_controller ();
/*
 * This function is a main loop that is supposed to control all TERMINAL nodes :
 * tell them when to send or receive data. However, its content should be
 * configured through the generated code. At this moment, its content
 * is more a stub taken from GAISLER example. We have to discuss with TASTE
 * folks to decide how to implement the communication policy deployed on
 * the controller from the AADL models.
 */

int   __po_hi_c_driver_1553_rasta_proccess_list (__po_hi_c_driver_rasta_1553_brm_t chan, struct bc_msg *list, int test);
/*
 * Function called by the controller to proccess a list of commands.
 * A command is a message that indicate if a node can send/receive data.
 */

#endif

#endif
