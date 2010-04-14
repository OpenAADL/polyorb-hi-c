/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2008, GET-Telecom Paris.
 */

#ifndef __PO_HI_COMMON_H__
#define __PO_HI_COMMON_H__

#include <deployment.h>

/*
 * Define some values that are dependant of the 
 * underlying executive.
 */
#if defined(POSIX)
   #include <stdlib.h>
   #include <stdio.h>
   #define __PO_HI_MAIN_NAME main
   #define __PO_HI_MAIN_TYPE int
   #define __PO_HI_MAIN_ARGS int argc , char *argv[] , char **arge
   #define __PO_HI_MAIN_RETURN EXIT_SUCCESS
   #define __ERRORMSG(s, args...) fprintf(stderr, s, ##args)
#elif defined(RTEMS_PURE)
   #define __PO_HI_MAIN_NAME Init
   #define __PO_HI_MAIN_TYPE rtems_task
   #define __PO_HI_MAIN_ARGS rtems_task_argument argument
   rtems_task Init (rtems_task_argument);
   #define __PO_HI_MAIN_RETURN 0
   #define __ERRORMSG(s, args...) fprintf(stderr, s, ##args)
#elif defined(RTEMS_POSIX)
   #define __PO_HI_MAIN_NAME POSIX_Init
   #define __PO_HI_MAIN_TYPE int
   #define __PO_HI_MAIN_ARGS 
   #define __PO_HI_MAIN_RETURN 0
   #define __ERRORMSG(s, args...) fprintf(stderr, s, ##args)
#endif

/*
 * Configure RTEMS executive.
 * We have to define the number of tasks inside the executive,
 * we deduce it from generated statements.
 */
#if defined(RTEMS_POSIX)
   #include <rtems.h>
   #include <inttypes.h>
   #include <bsp.h>
   #define CONFIGURE_INIT
   #define CONFIGURE_APPLICATION_NEEDS_CONSOLE_DRIVER
   #define CONFIGURE_APPLICATION_NEEDS_CLOCK_DRIVER

   int POSIX_Init ();
   #define CONFIGURE_MAXIMUM_POSIX_THREADS              __PO_HI_NB_TASKS + 2
   #define CONFIGURE_MAXIMUM_POSIX_CONDITION_VARIABLES  __PO_HI_NB_TASKS + 1
   #define CONFIGURE_MAXIMUM_POSIX_MUTEXES              __PO_HI_NB_TASKS + 1
   #define CONFIGURE_POSIX_INIT_THREAD_TABLE
   #include <po_hi_rtemsconfig.h>
   #include <rtems/confdefs.h>
#endif 

#endif /* __COMMON_H__ */
