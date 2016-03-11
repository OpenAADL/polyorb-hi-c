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
