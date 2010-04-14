/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2009, GET-Telecom Paris.
 */

#ifndef __PO_HI_UTILS_H__
#define __PO_HI_UTILS_H__

#include <po_hi_time.h>
#include <po_hi_types.h>

/*
 * Simulate the WCET of the task. It enters an infinite loop during a
 * random period chosen from the first and second argument.
 */
int __po_hi_simulate_wcet (__po_hi_time_t time1, __po_hi_time_t time2);

/*
 * Take a rate as argument, returns the probability that we meet this rate.
 */
int __po_hi_compute_miss (__po_hi_uint8_t rate);
#endif /* __PO_HI_UTILS_H__ */ 
