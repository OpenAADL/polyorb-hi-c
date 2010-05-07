/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2008, GET-Telecom Paris.
 * Copyright (C) 2010, European Space Agency.
 */

#ifndef __PO_HI_COMMON_H__
#define __PO_HI_COMMON_H__

#include <deployment.h>

/*
 * Configure RTEMS executive.
 * We have to define the number of tasks inside the executive,
 * we deduce it from generated statements.
 */
#if defined(RTEMS_POSIX)
   #include <rtems.h>
   #include <inttypes.h>
   #define CONFIGURE_INIT
   #include <bsp.h>
   #define CONFIGURE_APPLICATION_NEEDS_CONSOLE_DRIVER
   #define CONFIGURE_APPLICATION_NEEDS_CLOCK_DRIVER
   #define CONFIGURE_APPLICATION_NEEDS_NULL_DRIVER
   #define CONFIGURE_MAXIMUM_POSIX_TIMERS          40
   #define CONFIGURE_MAXIMUM_TIMERS                40


   int POSIX_Init ();
   #define CONFIGURE_MAXIMUM_POSIX_THREADS              __PO_HI_NB_TASKS + 4
   #define CONFIGURE_MAXIMUM_TASKS             16
   #define CONFIGURE_EXTRA_TASK_STACKS         (20 * RTEMS_MINIMUM_STACK_SIZE)
#ifdef __PO_HI_NB_PORTS
   #define CONFIGURE_MAXIMUM_POSIX_MUTEXES              __PO_HI_NB_TASKS + 2 + __PO_HI_NB_PORTS
   #define CONFIGURE_MAXIMUM_POSIX_CONDITION_VARIABLES  __PO_HI_NB_TASKS + 2 + __PO_HI_NB_PORTS
#else
   #define CONFIGURE_MAXIMUM_POSIX_MUTEXES              __PO_HI_NB_TASKS + 2 + __PO_HI_NB_PORTS
   #define CONFIGURE_MAXIMUM_POSIX_CONDITION_VARIABLES  __PO_HI_NB_TASKS + 2 + __PO_HI_NB_PORTS
#endif
   #define CONFIGURE_POSIX_INIT_THREAD_TABLE
   #include <po_hi_rtemsconfig.h>
   #include <rtems/confdefs.h>
#endif 

#endif /* __COMMON_H__ */
