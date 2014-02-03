/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://assert-project.net/taste
 *
 * Copyright (C) 2007-2009 Telecom ParisTech, 2010-2012 ESA & ISAE.
 */

#ifndef __PO_HI_TIME_H__
#define __PO_HI_TIME_H__

#include <po_hi_types.h>

#ifndef HAVE_CLOCK_GETTIME
#if defined (__CYGWIN__) || defined (__MINGW32__)
#else
#include <xlocale.h>
#endif

#include <time.h>
#endif

#ifdef XENO_NATIVE
#include <native/timer.h>
#include <native/task.h>
#endif


#ifdef _WIN32
#include <tchar.h>
#include <windows.h>

/*
 * Win32 helper functions to convert __po_hi_time_t to a representation
 * that would be suitable for Windows.
 */
unsigned __po_hi_windows_tick_to_unix_seconds(long long win_ticks);
LARGE_INTEGER __po_hi_unix_seconds_to_windows_tick(unsigned sec, unsigned nsec);
#endif

/*
 * Represent the time in PolyORB-HI.
 *
 * The value stored in this type depends on the system : on POSIX, it
 * is the epoch (time since 1970), on other systems, it can be the
 * number of elapsed ticks since the beginning of the program.
 *
 * The granularity of the time is in microsecond (10^-6)
 */
typedef struct
{
   __po_hi_uint32_t     sec;     /* amount of second     */
   __po_hi_uint32_t     nsec;    /* amount of nanosecond */
}__po_hi_time_t;

/*
 * An ACSL predicate to verify invariant on _po_hi_time_t.
 */

/*@
  @ predicate is_time_struct_correct(__po_hi_time_t *mytime) =
  @   mytime->sec >=0 &&
  @   mytime->nsec >=0 && mytime->nsec < 1000000000;
  @*/

#define __PO_HI_TIME_TO_US(value) ((value.sec*1000000)+(value.nsec / 1000))

#define __PO_HI_TIME_TO_MS(value) ((value.sec*1000)+(value.nsec / 1000000))

/*
 * Add specification for clock_gettime ensuring that the timespec
 * structure used in clock_gettime does not overlap with a ghost field
 * representing the __po_hi_time_t * parameter of __po_hi_get_time.
 */
//@ ghost __po_hi_time_t *time_struct_to_be_initialized;

/*@
  @ ensures \separated(time_struct_to_be_initialized, __tp);
  @*/
int clock_gettime (clockid_t __clock_id, struct timespec *__tp);

/*
 * Get the current time and store informations
 * in the structure mytime.
 * If there is an error, returns a negative value
 * (ERROR_CLOCK). Else, returns a positive value.
 *
 * For the ACSL specification, this function always returns
 * __PO_HI_SUCCESS as we do force POSIX. The specification also
 * precises the possible values for sec and nsec fields.
 *
 * Must include po_hi_returns.h to be able to use __PO_HI_SUCCESS
 * in specification, but does not seem to be possible... TBD
 */
/*@ requires \valid(mytime);
  @ ensures is_time_struct_correct(mytime);
  @ ensures \result == 1;
  @*/
int __po_hi_get_time (__po_hi_time_t* mytime);

/*@ requires \valid(result) &&
						 \valid(left)   &&
						 \valid(right);
		requires left->sec + right->sec + 1 <= 4294967295;
		requires left->nsec + right->nsec <= 4294967295;
		requires result != left && result != right;
		ensures \result == 1;
		assigns result->sec, result->nsec;
		behavior more_than_1s_in_nsec:
			assumes left->nsec + right->nsec > 1000000000;
			ensures result->sec == left->sec + right->sec + 1;
			ensures result->nsec == left->nsec + right->nsec - 1000000000;
		behavior equal_or_less_than_1s_in_nsec:
			assumes left->nsec + right->nsec <= 1000000000;
			ensures result->sec == left->sec + right->sec;
			ensures result->nsec == left->nsec + right->nsec;
		complete behaviors more_than_1s_in_nsec, equal_or_less_than_1s_in_nsec;
		disjoint behaviors more_than_1s_in_nsec, equal_or_less_than_1s_in_nsec;
*/
int __po_hi_add_times (__po_hi_time_t* result,
                       const __po_hi_time_t* left,
                       const __po_hi_time_t* right);
/*
 * Add the two structures given in parameter. The returned
 * value is the result of the operation.
 */

/*@ requires \valid(time);
		ensures time->sec == seconds;
		ensures time->nsec == 0;
		ensures \result == 1;
		assigns time->sec, time->nsec;
*/
int __po_hi_seconds (__po_hi_time_t* time,
                     const __po_hi_uint32_t seconds);
/*
 * Build a __po_hi_time_t value which contains the
 * amount of time (in seconds) represented by the
 * argument seconds.
 */

/*@ requires \valid(time);
		ensures time->sec == milliseconds / 1000;
		ensures time->nsec == (milliseconds - (time->sec * 1000)) * 1000000;
		ensures \result == 1;
		assigns time->sec, time->nsec;
*/
int __po_hi_milliseconds  (__po_hi_time_t* time,
                           const __po_hi_uint32_t milliseconds);
/*
 * Build a __po_hi_time_t value which contains the
 * amount of time (in milliseconds) represented by the
 * argument milliseconds.
 */

/*@ requires \valid(time);
		ensures time->sec == microseconds / 1000000;
		ensures time->nsec == (microseconds - (time->sec * 1000000)) * 1000;
		ensures \result == 1;
		assigns time->sec, time->nsec;
*/
int __po_hi_microseconds  (__po_hi_time_t* time, const __po_hi_uint32_t microseconds);
/*
 * Build a __po_hi_time_t value which contains the
 * amount of time (in microseconds) represented by the
 * argument microseconds.
 */


int __po_hi_delay_until (const __po_hi_time_t* time);
/*
 * sleep until the time given in argument.
 * Return SUCCESS if there is no error. Else, it returns
 * a negative value : ERROR_CLOCK or ERROR_PTHREAD_COND
 */

/*@ requires \valid(dst) && \valid(src);
  	requires \separated(dst, src);
  	requires src->nsec <= 1000000000;
		ensures dst->sec == src->sec;
		ensures dst->nsec == src->nsec;
		assigns dst->sec, dst->nsec;
*/
int __po_hi_time_copy (__po_hi_time_t* dst, const __po_hi_time_t* src);
/*
 * Copy a time value from src to dst.
 * Returns __PO_HI_SUCCESS if successful.
 */


#ifdef NEED_CLOCK_GETTIME
#define CLOCK_REALTIME 0
int clock_gettime(int clk_id, struct timespec *tp);
#endif
/*
 * If the system doesn't support the clock_gettime function, we
 * emulate it. For example, Darwin does not support it
 */

/*@ requires \valid(value) &&
						 \valid(limit);
		assigns \nothing;
		behavior value_sec_higher_than_limit_sec:
			assumes value->sec > limit->sec;
			ensures \result == 1;
		behavior value_sec_equal_to_limit_sec_and_value_nsec_higher_than_limit_nsec:
			assumes value->sec == limit->sec && value->nsec > limit->nsec;
			ensures \result == 1;
		behavior value_sec_equal_to_limit_sec_and_value_nsec_lower_than_limit_nsec:
			assumes value->sec == limit->sec && value->nsec <= limit->nsec;
			ensures \result == 0;
		behavior value_sec_lower_than_limit_sec:
			assumes value->sec < limit->sec;
			ensures \result == 0;
		complete behaviors value_sec_higher_than_limit_sec,
											 value_sec_equal_to_limit_sec_and_value_nsec_higher_than_limit_nsec,
											 value_sec_equal_to_limit_sec_and_value_nsec_lower_than_limit_nsec,
											 value_sec_lower_than_limit_sec;
		disjoint behaviors value_sec_higher_than_limit_sec,
											 value_sec_equal_to_limit_sec_and_value_nsec_higher_than_limit_nsec,
											 value_sec_equal_to_limit_sec_and_value_nsec_lower_than_limit_nsec,
											 value_sec_lower_than_limit_sec;
*/
int __po_hi_time_is_greater (const __po_hi_time_t* value, const __po_hi_time_t* limit);
/*
 * Indicates if a time value is greater than an other.
 * Returns 1 if value is greater than limit.
 * Returns 0 otherwise.
 */

#include <errno.h>
#ifndef ETIMEDOUT
#define ETIMEDOUT 60
#endif
/*
 * Ensure that ETIMEDOUT is defined
 * Workaround for bug #286
 */

#endif /* __PO_HI_TIME_H__ */
