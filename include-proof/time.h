/**************************************************************************/
/*                                                                        */
/*  This file is part of Frama-C.                                         */
/*                                                                        */
/*  Copyright (C) 2007-2015                                               */
/*    CEA (Commissariat à l'énergie atomique et aux énergies              */
/*         alternatives)                                                  */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 2.1.                                              */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 2.1                 */
/*  for more details (enclosed in the file licenses/LGPLv2.1).            */
/*                                                                        */
/**************************************************************************/

#ifndef __FC_TIME_H
#define __FC_TIME_H
#include "__fc_define_null.h"
#include "__fc_define_size_t.h"
#include "__fc_define_restrict.h"

/*
 * Names of the interval timers, and structure
 * defining a timer setting:
 */
#define	ITIMER_REAL		0
#define	ITIMER_VIRTUAL		1
#define	ITIMER_PROF		2


typedef unsigned int clock_t;
#include "__fc_define_time_t.h"
#define CLOCKS_PER_SEC ((time_t)16000)

struct tm {
  int tm_sec; // seconds after the minute [0, 60]
  int tm_min; // minutes after the hour [0, 59]
  int tm_hour; // hours since midnight [0, 23]
  int tm_mday; // day of the month [1, 31]
  int tm_mon; // months since January [0, 11]
  int tm_year; // years since 1900
  int tm_wday; // days since Sunday [0, 6]
  int tm_yday; // days since January 1 [0, 365]
  int tm_isdst; // Daylight Saving Time flag
};

#include "__fc_define_timespec.h"

struct itimerspec {
  struct timespec  it_interval;
  struct timespec  it_value;
};



#define CLOCK_REALTIME 666
#define CLOCK_MONOTONIC 1
#define TIMER_ABSTIME 0

unsigned int __fc_time_model __attribute__((FRAMA_C_MODEL));

/*@ assigns __fc_time_model \from __fc_time_model;
  assigns \result \from __fc_time_model; */
clock_t clock(void);

/*@ assigns \result \from time1, time0; */
double difftime(time_t time1, time_t time0);

/*@ assigns *timeptr, \result \from *timeptr; */
time_t mktime(struct tm *timeptr);

/*@ assigns __fc_time_model \from __fc_time_model;
  assigns *timer, \result \from __fc_time_model; */
time_t time(time_t *timer);

char *asctime(const struct tm *timeptr);

char *ctime(const time_t *timer);

struct tm __fc_time_tm;
struct tm * const  __fc_time_tm_ptr=&__fc_time_tm;

/*@ assigns \result \from __fc_time_tm_ptr;
  assigns __fc_time_tm \from *timer;
  ensures \result == &__fc_time_tm || \result == \null ;
*/
struct tm *gmtime(const time_t *timer);

/*@ assigns \result \from __fc_time_tm_ptr;
  assigns __fc_time_tm \from *timer;
  ensures \result == &__fc_time_tm || \result == \null;
*/
struct tm *localtime(const time_t *timer);

size_t strftime(char * restrict s,
		size_t maxsize,
		const char * restrict format,
		const struct tm * restrict timeptr);

/* POSIX */
int nanosleep(const struct timespec *, struct timespec *);

extern int daylight;
extern long timezone;
extern char *tzname[2];
/* assigns tzname[0..1][0..] \from \nothing ;*/
void tzset(void);

/*******************************************************************
 * Addings for the PolyORB-HI/C project
 *
 * Original file taken from `frama-c -print-share-path`/libc/time.h
 *******************************************************************/

/* including stdint.h and asm-generic/errno-base.h to be able to use
 * constants in specifications
 */
#include <errno.h>
#include <stdint.h>

/* need __clockid_t, original time.h from libc use conditions, but we do
 * not care ;)
 */
# include <types.h>

/* Clock ID used in clock and timer functions.  */
/* Lots of include from bits dir skipped...     */
typedef int clockid_t;

/* needed in specification ? */
#define CLOCK_REALTIME_COARSE    667
#define CLOCK_MONOTONIC_COARSE   668
#define CLOCK_MONOTONIC_RAW      669
#define CLOCK_BOOTTIME           670
#define CLOCK_PROCESS_CPUTIME_ID 671
#define CLOCK_THREAD_CPUTIME_ID  672

/* ACSL predicate for verifying validity of clock identifiers. Must be
 * parametrized. TBD.
 */
/*@ predicate clock_valid(clockid_t clock_id) =
  @   clock_id == CLOCK_REALTIME &&
  @   clock_id == CLOCK_REALTIME_COARSE &&
  @   clock_id == CLOCK_MONOTONIC &&
  @   clock_id == CLOCK_MONOTONIC_COARSE &&
  @   clock_id == CLOCK_MONOTONIC_RAW &&
  @   clock_id == CLOCK_BOOTTIME &&
  @   clock_id == CLOCK_PROCESS_CPUTIME_ID &&
  @   clock_id == CLOCK_THREAD_CPUTIME_ID;
  @*/

/* Get current value of clock CLOCK_ID and store it in TP.
 *
 * Add an ACSL specification saying that when calling clock_gettime is
 * successful:
 *  - clock_gettime allocates __tp and __tp is valid
 *  - values of __tp fields are correct
 *
 * Behaviors have been defined for error cases. Notice that it should
 * be necessary to look more precisely at clock_gettime code to verify
 * that the postconditions on __tp fields can be ensured.
 */
/*@ behavior __tp_not_valid:
  @   assumes !\valid(__tp);
  @   assigns \nothing;
  @   ensures \result == EFAULT;
  @ behavior clock_not_valid:
  @   assumes !clock_valid(__clock_id);
  @   assigns \nothing;
  @   ensures \result == EINVAL;
  @ behavior normal:
  @   assumes \valid(__tp);
  @   assigns __tp->tv_sec;
  @   assigns __tp->tv_nsec;
  @   ensures \result == 0;
  @   ensures \valid(__tp);
  @   ensures __tp == \old(__tp);
  @   ensures __tp->tv_sec >= 0 && __tp->tv_sec <= UINT32_MAX;
  @   ensures __tp->tv_nsec < 1000000000 && __tp->tv_nsec >= 0;
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
extern int clock_gettime (clockid_t __clock_id, struct timespec *__tp); // __THROW;

#endif
