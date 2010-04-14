/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2008, GET-Telecom Paris.
 */

#ifndef __PO_HI_TIME_H__
#define __PO_HI_TIME_H__

#include <po_hi_types.h>

#ifndef HAVE_CLOCK_GETTIME
#include <time.h>
#endif


typedef __po_hi_uint64_t __po_hi_time_t;
/*
 * Represent the time in PolyORB-HI.
 *
 * The value stored in this type depends on the system : on POSIX, it
 * is the epoch (time since 1970), on other systems, it can be the
 * number of elapsed ticks since the beginning of the program.
 *
 * The granularity of the time is in microsecond (10^-6)
 */

int __po_hi_get_time (__po_hi_time_t* mytime);
/*
 * Get the current time and store informations
 * in the structure mytime.
 * If there is an error, returns a negative value
 * (ERROR_CLOCK). Else, returns a positive value.
 */

__po_hi_time_t __po_hi_add_times (__po_hi_time_t left, 
				  __po_hi_time_t right);
/*
 * Add the two structures given in parameter. The returned
 * value is the result of the operation.
 */

__po_hi_time_t __po_hi_seconds (__po_hi_uint32_t seconds);
/*
 * Build a __po_hi_time_t value which contains the
 * amount of time (in seconds) represented by the
 * argument seconds.
 */

__po_hi_time_t __po_hi_milliseconds (__po_hi_uint32_t milliseconds);
/*
 * Build a __po_hi_time_t value which contains the
 * amount of time (in milliseconds) represented by the
 * argument milliseconds.
 */

__po_hi_time_t __po_hi_microseconds (__po_hi_uint32_t microseconds);
/*
 * Build a __po_hi_time_t value which contains the
 * amount of time (in microseconds) represented by the
 * argument microseconds.
 */

int __po_hi_delay_until (__po_hi_time_t time);
/*
 * sleep until the time given in argument.
 * Return SUCCESS if there is no error. Else, it returns
 * a negative value : ERROR_CLOCK or ERROR_PTHREAD_COND
 */

#ifdef NEED_CLOCK_GETTIME
#define CLOCK_REALTIME 0
int clock_gettime(int clk_id, struct timespec *tp);
#endif
/*
 * If the system doesn't support the clock_gettime function, we
 * emulate it. For example, Darwin does not support it
 */

#endif /* __PO_HI_TIME_H__ */
