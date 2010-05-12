/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2008, GET-Telecom Paris.
 */

#ifndef __PO_HI_MAIN__
#define __PO_HI_MAIN__

int __po_hi_initialize ();
/*
 * Invoke all functions to initialize tasks 
 * and network. Return __PO_HI_SUCCESS if there
 * is no error. Else, it can return the value
 * __PO_HI_ERROR_PTHREAD_BARRIER.
 */

void __po_hi_initialize_add_task ();
/*
 * Declare that another task has to be initialized
 */

int __po_hi_wait_initialization ();
/*
 * Invoked by each node to wait initialization
 * of other node. It is used by synchronize all
 * processes.
 * Return __PO_HI_SUCCESS value is there is no
 * error. Return __PO_HI_ERROR_PTHREAD_BARRIER
 * if there is an error.
 */

#ifdef __PO_HI_USE_GPROF
void __po_hi_wait_end_of_instrumentation ();
/*
 * Wait a certain amount of time to finish the 
 * execution of the system.
 */
#endif

#endif /* __PO_HI_MAIN__ */
