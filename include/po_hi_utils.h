/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://www.openaadl.org
 *
 * Copyright (C) 2007-2009 Telecom ParisTech, 2010-2019 ESA & ISAE, 2019-2021 OpenAADL
 */

#ifndef __PO_HI_UTILS_H__
#define __PO_HI_UTILS_H__

#include <po_hi_time.h>
#include <po_hi_types.h>

/*
 * Take a rate as argument, returns the probability that we meet this rate.
 */
int __po_hi_compute_miss(
  __po_hi_uint8_t rate);

unsigned long __po_hi_swap_byte(
  unsigned long value);

#if defined(__PO_HI_USE_VCD) && defined(__unix__)
#include <pthread.h>
#include <string.h>
#include <deployment.h>

/* Types used to store the vcd trace */
typedef struct {
  __po_hi_vcd_event_kind_t vcd_event_kind;
  uint64_t __po_hi_vcd_trace_timestamp;
  __po_hi_task_id task_id;
  __po_hi_local_port_t port_id;
  __po_hi_port_id_t port_queue_used_size;

} __po_hi_vcd_trace_element_t;

/* __po_hi_vcd_trace_max_nb_events used to reallocate the array
 * of the vcd trace */
extern __po_hi_int32_t __po_hi_vcd_trace_max_nb_events;

/* __po_hi_vcd_trace_array an array containing the vcd trace
 * as elements with type __po_hi_vcd_trace_element_t  */
extern __po_hi_vcd_trace_element_t *__po_hi_vcd_trace_array;

/* __po_hi_vcd_trace_array_index is the index of __po_hi_vcd_trace_array
 * it should be protected as it is shared between tasks used to
 * save a new element in the array*/
extern __po_hi_int32_t __po_hi_vcd_trace_array_index;

/* mutex used to protect the index __po_hi_vcd_trace_array_index */
extern pthread_mutex_t __po_hi_vcd_trace_mutex;

/* __po_hi_get_larger_array_for_vcd_trace allows to reallocate a larger
 * array to save the vcd trace */
void __po_hi_get_larger_array_for_vcd_trace(
  void);

/* __po_hi_save_event_in_vcd_trace allows to save an element in
 * __po_hi_vcd_trace_array */
void __po_hi_save_event_in_vcd_trace(
  uint64_t timestamp,
  __po_hi_vcd_event_kind_t event_kind,
  __po_hi_task_id task,
  __po_hi_local_port_t port,
  __po_hi_port_id_t queue_size);

/* __po_hi_compute_timestamp : returns the actual instant
 * based on the __po_hi_vcd_start_t instant. The returned
 * value is in (ms) */
uint64_t __po_hi_compute_timestamp(
  void);

/* __po_hi_vcd_start_t is the start time and it is
 * set in the procedure __po_hi_initialize_vcd_trace */
extern __po_hi_time_t __po_hi_vcd_start_t;

/* __po_hi_signalHandler is a SIGINT signal handler : it is invoked when
 * Ctrl-c is pressed in the keyboard to interrupt the execution
 * of the application. This handler allows a normal exit
 * of the program which enables the invocation
 * of the atexit function */
void __po_hi_signalHandler(
  int signo);

/* __po_hi_signalHandler create the vcd file and fill it
 * with the vcd trace saved in __po_hi_vcd_trace_array */
void __po_hi_create_vcd_file(
  int);

/* __po_hi_initialize_vcd_trace initializes some variables and catches
 * the SIGINT signal*/
void __po_hi_initialize_vcd_trace(
  void);

/* Variable keeping track of whether VCD tracing is enabled or not */
enum tagVCD {
  VCD_UNCHECKED,
  VCD_DISABLED,
  VCD_ENABLED
};

void __po_hi_instrumentation_vcd_init(
  void);

#define __PO_HI_INITIALIZE_VCD_TRACE __po_hi_initialize_vcd_trace ();
#else
#define __PO_HI_INITIALIZE_VCD_TRACE
#endif
#endif /* __PO_HI_UTILS_H__ */
