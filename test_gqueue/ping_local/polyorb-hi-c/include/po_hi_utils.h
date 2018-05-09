/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2007-2009 Telecom ParisTech, 2010-2017 ESA & ISAE.
 */

#ifndef __PO_HI_UTILS_H__
#define __PO_HI_UTILS_H__

#include <po_hi_time.h>
#include <po_hi_types.h>

/*
 * Take a rate as argument, returns the probability that we meet this rate.
 */
int __po_hi_compute_miss (__po_hi_uint8_t rate);

unsigned long __po_hi_swap_byte (unsigned long value);

#if defined(__PO_HI_USE_VCD) && defined(__unix__)

#include <pthread.h>
#include <string.h>

/* Variable keeping track of whether VCD tracing is enabled or not */
enum tagVCD {
    VCD_UNCHECKED,
    VCD_DISABLED,
    VCD_ENABLED
};

void __po_hi_instrumentation_vcd_init (void);

#define __PO_HI_INSTRUMENTATION_VCD_INIT __po_hi_instrumentation_vcd_init ();

#define __PO_HI_INSTRUMENTATION_VCD_WRITE(s, args...)                          \
   {                                                                           \
      extern enum tagVCD VCD_state;                                            \
      if (VCD_state == VCD_ENABLED) {                                          \
          extern int               __po_hi_vcd_file;                           \
          extern __po_hi_time_t    __po_hi_vcd_start_time;                     \
          extern pthread_mutex_t   __po_hi_vcd_mutex;                          \
          __po_hi_time_t           __po_hi_vcd_current_time;                   \
          char                    buf[1024];                                   \
          int                     size_to_write = 0;                           \
          uint64_t                st,ct,et = 0;                                \
                                                                               \
          pthread_mutex_lock (&__po_hi_vcd_mutex);                             \
                                                                               \
          if (__po_hi_get_time(&__po_hi_vcd_current_time) != __PO_HI_SUCCESS)  \
          {                                                                    \
             __DEBUGMSG("[POHIC-INSTRUMENTATION] Could not retrieve time\n");  \
          }                                                                    \
          else                                                                 \
          {                                                                    \
             st = __PO_HI_TIME_TO_US(__po_hi_vcd_start_time);                  \
             ct = __PO_HI_TIME_TO_US(__po_hi_vcd_current_time);                \
             et = ct - st ;                                                    \
             memset (buf, '\0', 1024);                                         \
             size_to_write = sprintf (buf, "#%llu\n", et);                     \
             write (__po_hi_vcd_file, buf, size_to_write);                     \
                                                                               \
             memset (buf, '\0', 1024);                                         \
             size_to_write = sprintf (buf, s, ##args);                         \
             write (__po_hi_vcd_file, buf, size_to_write);                     \
          }                                                                    \
          pthread_mutex_unlock (&__po_hi_vcd_mutex);                           \
      }                                                                        \
   }
#else
   #define __PO_HI_INSTRUMENTATION_VCD_WRITE(s, args...)
   #define __PO_HI_INSTRUMENTATION_VCD_INIT
#endif

#endif /* __PO_HI_UTILS_H__ */
