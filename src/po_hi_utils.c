/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://www.openaadl.org
 *
 * Copyright (C) 2007-2009 Telecom ParisTech, 2010-2019 ESA & ISAE, 2019-2021 OpenAADL
 */

#include <po_hi_config.h>
#include <po_hi_time.h>
#include <po_hi_types.h>
#include <po_hi_debug.h>
#include <po_hi_utils.h>
#include <stdlib.h>
#include <signal.h>
#include <unistd.h>
#include <inttypes.h>

/* Header files in PolyORB-HI */

#include <deployment.h>
/* Header files from generated code */

#include <stdlib.h>

#if defined(__PO_HI_USE_VCD) && defined(__unix__)

/* __po_hi_vcd_trace_max_nb_events used to reallocate the array
 * of the vcd trace */
__po_hi_int32_t __po_hi_vcd_trace_max_nb_events;

/* __po_hi_vcd_trace_array an array containing the vcd trace
 * as elements with type __po_hi_vcd_trace_element_t  */
__po_hi_vcd_trace_element_t *__po_hi_vcd_trace_array;

/* __po_hi_vcd_trace_array_index is the index of __po_hi_vcd_trace_array
 * it should be protected as it is shared between tasks used to
 * save a new element in the array*/
__po_hi_int32_t __po_hi_vcd_trace_array_index;

/* mutex used to protect the index __po_hi_vcd_trace_array_index */
pthread_mutex_t __po_hi_vcd_trace_mutex;

/* __po_hi_vcd_start_t is the start time and it is
 * set in the procedure __po_hi_initialize_vcd_trace */
__po_hi_time_t __po_hi_vcd_start_t;
#endif

int __po_hi_compute_miss(
  __po_hi_uint8_t rate) {
  int v;

  v = rand() % 100;

  if (v <= rate) {
    return 0;
  }

  return 1;
}


unsigned long __po_hi_swap_byte(
  unsigned long value) {
  union u {
    unsigned long vi;
    unsigned char c[sizeof(unsigned long)];
  };
  union v {
    unsigned long ni;
    unsigned char d[sizeof(unsigned long)];
  };
  union u un;
  union v vn;

  un.vi = value;
  vn.d[0] = un.c[3];
  vn.d[1] = un.c[2];
  vn.d[2] = un.c[1];
  vn.d[3] = un.c[0];
  return (vn.ni);
}

#if defined(__PO_HI_USE_VCD) && defined(__unix__)
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <pthread.h>
#include <fcntl.h>
#include <time.h>

#include <po_hi_returns.h>

#include <deployment.h>

enum tagVCD VCD_state = VCD_UNCHECKED;

int __po_hi_vcd_file;

#if __PO_HI_NB_PORTS > 0
extern __po_hi_int8_t *__po_hi_gqueues_sizes[__PO_HI_NB_TASKS];
extern __po_hi_uint8_t *__po_hi_gqueues_used_size[__PO_HI_NB_TASKS];
extern __po_hi_port_id_t __po_hi_gqueues_nb_ports[__PO_HI_NB_TASKS];
#endif

uint64_t __po_hi_compute_timestamp(
  ) {
  __po_hi_time_t ct;
  uint64_t ts = 0;

  __po_hi_get_time(&ct);
  ts = __PO_HI_TIME_TO_US(ct) - __PO_HI_TIME_TO_US(__po_hi_vcd_start_t);
  return ts;
}

void __po_hi_get_larger_array_for_vcd_trace(
  ) {
  __po_hi_vcd_trace_element_t *tmp;

  __po_hi_vcd_trace_max_nb_events += 100;
  tmp = (__po_hi_vcd_trace_element_t *) realloc(__po_hi_vcd_trace_array, __po_hi_vcd_trace_max_nb_events * sizeof(__po_hi_vcd_trace_element_t));        // get a new larger array
  __po_hi_vcd_trace_array = tmp;
}

void __po_hi_save_event_in_vcd_trace(
  uint64_t timestamp,
  __po_hi_vcd_event_kind_t event_kind,
  __po_hi_task_id task,
  __po_hi_local_port_t port,
  __po_hi_port_id_t queue_size) {
  __po_hi_int32_t current_index;

  /* lock the mutex to save the current index of
   * the vcd trace array and then increment it*/
  pthread_mutex_lock(&__po_hi_vcd_trace_mutex);
  current_index = __po_hi_vcd_trace_array_index;
  /* if the vcd trace array reach the maximum allocated size
   * we increase its size*/
  if (current_index == __po_hi_vcd_trace_max_nb_events)
    __po_hi_get_larger_array_for_vcd_trace();
  __po_hi_vcd_trace_array_index++;
  pthread_mutex_unlock(&__po_hi_vcd_trace_mutex);


  /* Save the instant of the dispatch event of the task
   * in the __po_hi_vcd_trace_timestamps array */
  __po_hi_vcd_trace_array[current_index].vcd_event_kind = event_kind;
  __po_hi_vcd_trace_array[current_index].__po_hi_vcd_trace_timestamp =
    timestamp;
  __po_hi_vcd_trace_array[current_index].task_id = task;
  __po_hi_vcd_trace_array[current_index].port_id = port;
  __po_hi_vcd_trace_array[current_index].port_queue_used_size = queue_size;

}

void __po_hi_signalHandler(
  int signo) {
  if (signo == SIGINT)
    exit(EXIT_SUCCESS);
}

void __po_hi_initialize_vcd_trace(
  ) {
  if (VCD_state == VCD_UNCHECKED) {
    VCD_state = NULL == getenv("VCD_ENABLED") ? VCD_DISABLED : VCD_ENABLED;
  }

  if (VCD_state != VCD_ENABLED) {
    return;
  }

  /* capture the start time of execution */
  __po_hi_get_time(&__po_hi_vcd_start_t);

  /* initialize mutex to protect the index of the array
   * in which the vcd trace is saved */
  pthread_mutex_init(&__po_hi_vcd_trace_mutex, NULL);

  /* Catch the SIGINT signal */
  signal(SIGINT, __po_hi_signalHandler);
  /* Catch the SIGUSR1 signal to store the vcd file at any time */
  signal(SIGUSR1, __po_hi_create_vcd_file);
}

void __po_hi_instrumentation_vcd_init(
  ) {

#if __PO_HI_NB_PORTS > 0
  int port, task;
#endif

  int i;
  char buf[1024];
  int size_to_write = 0;
  time_t current_time;
  char __po_hi_vcd_filename[100];

  sprintf(__po_hi_vcd_filename, "%s.vcd", __PO_HI_MY_NODE_NAME);
  __po_hi_vcd_file =
    open(__po_hi_vcd_filename, O_WRONLY | O_CREAT | O_SYNC,
         S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH);
  if (__po_hi_vcd_file > 0) {
    write(__po_hi_vcd_file, "$date\n", 6);

    memset(buf, '\0', 1024);
    time(&current_time);
    size_to_write = sprintf(buf, "%s", ctime(&current_time));
    write(__po_hi_vcd_file, buf, size_to_write);

    write(__po_hi_vcd_file, "$end\n", 5);
    write(__po_hi_vcd_file, "$version\n", 9);
    write(__po_hi_vcd_file, "VCD generator tool version info text.\n", 38);
    write(__po_hi_vcd_file, "$end\n", 5);
    write(__po_hi_vcd_file, "$comment\n", 9);
    write(__po_hi_vcd_file,
          "This file has been create by polyorb-hi-c runtime of ocarina.\n",
          62);
    write(__po_hi_vcd_file, "$end\n", 5);
    write(__po_hi_vcd_file, "$timescale 1us $end\n", 20);
    write(__po_hi_vcd_file, "$scope module tasks $end\n", 25);
    for (i = 0; i < __PO_HI_NB_TASKS; i++) {
      memset(buf, '\0', 1024);
      size_to_write = sprintf(buf, "$var wire 1 t%d task_%d $end\n", i, i);
      write(__po_hi_vcd_file, buf, size_to_write);
    }
    write(__po_hi_vcd_file, "$upscope $end\n", 14);

#if __PO_HI_NB_PROTECTED > 0
    write(__po_hi_vcd_file, "$scope module mutexes $end\n", 27);
    for (i = 0; i < __PO_HI_NB_PROTECTED; ++i) {
      memset(buf, '\0', 1024);
      size_to_write = sprintf(buf, "$var wire 1 w%i awaited_%i $end\n", i, i);
      write(__po_hi_vcd_file, buf, size_to_write);
    }
    for (i = 0; i < __PO_HI_NB_PROTECTED; ++i) {
      memset(buf, '\0', 1024);
      size_to_write = sprintf(buf, "$var wire 1 l%i locked_%i $end\n", i, i);
      write(__po_hi_vcd_file, buf, size_to_write);
    }
    write(__po_hi_vcd_file, "$upscope $end\n", 14);
#endif

#if __PO_HI_NB_PORTS > 0
    write(__po_hi_vcd_file, "$scope module ports $end\n", 25);
    for (task = 0; task < __PO_HI_NB_TASKS; task++) {
      for (port = 0; port < __po_hi_gqueues_nb_ports[task]; port++) {

        if (__po_hi_gqueues_sizes[task][port] > 0) {

          memset(buf, '\0', 1024);
          size_to_write =
            sprintf(buf, "$var real %i p%i.%i port_%i_%i $end\n",
                    __po_hi_gqueues_sizes[task][port], task, port, task,
                    port);
          write(__po_hi_vcd_file, buf, size_to_write);
        }
      }
    }
    write(__po_hi_vcd_file, "$upscope $end\n", 14);
#endif

    write(__po_hi_vcd_file, "$enddefinitions $end\n", 21);
    write(__po_hi_vcd_file, "$dumpvars\n", 10);
    for (i = 0; i < __PO_HI_NB_TASKS; i++) {
      memset(buf, '\0', 1024);
      size_to_write = sprintf(buf, "0t%d\n", i);
      write(__po_hi_vcd_file, buf, size_to_write);
    }

#if __PO_HI_NB_PROTECTED > 0
    for (i = 0; i < __PO_HI_NB_PROTECTED; ++i) {
      memset(buf, '\0', 1024);
      size_to_write = sprintf(buf, "0w%d\n", i);
      write(__po_hi_vcd_file, buf, size_to_write);
    }
    for (i = 0; i < __PO_HI_NB_PROTECTED; ++i) {
      memset(buf, '\0', 1024);
      size_to_write = sprintf(buf, "0l%d\n", i);
      write(__po_hi_vcd_file, buf, size_to_write);
    }
#endif

#if __PO_HI_NB_PORTS > 0
    for (task = 0; task < __PO_HI_NB_TASKS; ++task) {
      for (port = 0; port < __po_hi_gqueues_nb_ports[task]; ++port) {
        if (__po_hi_gqueues_sizes[task][port] > 0) {
          memset(buf, '\0', 1024);
          size_to_write = sprintf(buf, "r0 p%d.%d\n", task, port);
          write(__po_hi_vcd_file, buf, size_to_write);
        }
      }
    }
#endif

    write(__po_hi_vcd_file, "$end\n", 5);

  } else {
    __DEBUGMSG("[POHIC-INSTRUMENTATION] Could not create file !\n");
  }
}

void __po_hi_create_vcd_file(
  int signo) {
  char buf[1024];
  int size_to_write = 0;

  (void) signo;
  __po_hi_instrumentation_vcd_init();
  printf("__po_hi_vcd_trace_array_index = %d \n",
         __po_hi_vcd_trace_array_index);
  for (int i = 0; i < __po_hi_vcd_trace_array_index; i++) {
    memset(buf, '\0', 1024);
    size_to_write =
      sprintf(buf, "#%" PRIu64 "\n",
              __po_hi_vcd_trace_array[i].__po_hi_vcd_trace_timestamp);
    write(__po_hi_vcd_file, buf, size_to_write);

    memset(buf, '\0', 1024);
    if (__po_hi_vcd_trace_array[i].vcd_event_kind ==
        __po_hi_task_wait_dispatch)
      size_to_write =
        sprintf(buf, "0t%d\n", __po_hi_vcd_trace_array[i].task_id);
    else if (__po_hi_vcd_trace_array[i].vcd_event_kind ==
             __po_hi_task_dispatched)
      size_to_write =
        sprintf(buf, "1t%d\n", __po_hi_vcd_trace_array[i].task_id);
    else if (__po_hi_vcd_trace_array[i].vcd_event_kind ==
             __po_hi_store_in_port_queue
             || __po_hi_vcd_trace_array[i].vcd_event_kind ==
             __po_hi_next_value_port_queue)
      size_to_write =
        sprintf(buf, "r%d p%d.%d\n",
                __po_hi_vcd_trace_array[i].port_queue_used_size,
                __po_hi_vcd_trace_array[i].task_id,
                __po_hi_vcd_trace_array[i].port_id);

    write(__po_hi_vcd_file, buf, size_to_write);

  }
}
#endif
