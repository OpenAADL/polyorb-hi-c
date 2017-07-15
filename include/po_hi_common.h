/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2007-2009 Telecom ParisTech, 2010-2014 ESA & ISAE.
 */

#ifndef __PO_HI_COMMON_H__
#define __PO_HI_COMMON_H__

#include <deployment.h>

#if (defined (RTEMS_POSIX) || defined (RTEMS_PURE))
   #if defined (__PO_HI_NEED_DRIVER_ETH_LEON) || \
       defined (__PO_HI_NEED_DRIVER_ETH_LEON_SENDER) || \
       defined (__PO_HI_NEED_DRIVER_ETH_LEON_RECEIVER)
   #define RTEMS_BSP_NETWORK_DRIVER_ATTACH RTEMS_BSP_NETWORK_DRIVER_ATTACH_SMC91111
   #endif
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
   #define CONFIGURE_APPLICATION_NEEDS_CONSOLE_DRIVER
   #define CONFIGURE_APPLICATION_NEEDS_CLOCK_DRIVER
   #define CONFIGURE_APPLICATION_NEEDS_NULL_DRIVER
//   #define CONFIGURE_APPLICATION_NEEDS_TIMER_DRIVER
   #define CONFIGURE_MAXIMUM_DRIVERS                     10
   #define CONFIGURE_MAXIMUM_POSIX_TIMERS                40
   #define CONFIGURE_MAXIMUM_TIMERS                      40
   #define CONFIGURE_EXECUTIVE_RAM_SIZE                  (512*1024)
   #define CONFIGURE_MAXIMUM_SEMAPHORES                  20
   #define CONFIGURE_MAXIMUM_TASKS                       __PO_HI_NB_TASKS + 2
   #define CONFIGURE_LIBIO_MAXIMUM_FILE_DESCRIPTORS      20

   int POSIX_Init ();
   #define CONFIGURE_MAXIMUM_POSIX_THREADS               __PO_HI_NB_TASKS + 10
/*   #define CONFIGURE_EXTRA_TASK_STACKS                   (20 * RTEMS_MINIMUM_STACK_SIZE)
 */
#ifdef __PO_HI_NB_PORTS
   #define CONFIGURE_MAXIMUM_POSIX_MUTEXES              __PO_HI_NB_TASKS + 10 + __PO_HI_NB_PORTS
   #define CONFIGURE_MAXIMUM_POSIX_CONDITION_VARIABLES  __PO_HI_NB_TASKS + 10 + __PO_HI_NB_PORTS
#else
   #define CONFIGURE_MAXIMUM_POSIX_MUTEXES              __PO_HI_NB_TASKS + 10 + __PO_HI_NB_PORTS
   #define CONFIGURE_MAXIMUM_POSIX_CONDITION_VARIABLES  __PO_HI_NB_TASKS + 10 + __PO_HI_NB_PORTS
#endif
   #define CONFIGURE_POSIX_INIT_THREAD_TABLE
   #define CONFIGURE_USE_IMFS_AS_BASE_FILESYSTEM

   #define CONFIGURE_INIT
   #include <rtems/confdefs.h>

#endif  /* RTEMS_POSIX */

#if defined(RTEMS_PURE)
   #include <rtems.h>
   #include <inttypes.h>
   #define CONFIGURE_INIT
   #include <bsp.h>

   #define CONFIGURE_APPLICATION_NEEDS_CONSOLE_DRIVER
   #define CONFIGURE_APPLICATION_NEEDS_CLOCK_DRIVER
   #define CONFIGURE_APPLICATION_NEEDS_NULL_DRIVER
// #define CONFIGURE_APPLICATION_NEEDS_TIMER_DRIVER
   #define CONFIGURE_MAXIMUM_DRIVERS                     10
   #define CONFIGURE_MAXIMUM_TIMERS                   40

#ifndef XM3_RTEMS_MODE
   #define CONFIGURE_EXECUTIVE_RAM_SIZE               (512*1024)
#endif
   /*
   #define CONFIGURE_MAXIMUM_SEMAPHORES               __PO_HI_NB_TASKS + (__PO_HI_NB_PORTS + 1) * 2 + __PO_HI_NB_PROTECTED + 1
   */
   #define CONFIGURE_MAXIMUM_SEMAPHORES               20
   #define CONFIGURE_MAXIMUM_TASKS                    __PO_HI_NB_TASKS + 5
   #define CONFIGURE_LIBIO_MAXIMUM_FILE_DESCRIPTORS   20
   #define CONFIGURE_MAXIMUM_PERIODS                  __PO_HI_NB_TASKS + 5
   /*
    * We put __PO_HI_NB_TASKS + 5 because we may have additional tasks
    * from the driver. Originally, it was +2 fr th emain thread and a potential
    * network thread. Since, other drivers take additional tasks and so, we
    * increase it to 5. We would do a better integration by filtering
    * the use of each driver.
    */

#ifndef RTEMS411
   rtems_task Init (rtems_task_argument no_argument);
#endif

   #define CONFIGURE_EXTRA_TASK_STACKS                __PO_HI_TASKS_STACK

   #define CONFIGURE_USE_IMFS_AS_BASE_FILESYSTEM
   #define CONFIGURE_RTEMS_INIT_TASKS_TABLE
   #define CONFIGURE_MAXIMUM_BARRIERS                 1 + __PO_HI_NB_PORTS + 1

   #include <rtems/confdefs.h>
#endif  /* RTEMS_PURE */

#if defined (X86_RTEMS) && defined (__PO_HI_USE_TRANSPORT) && __PO_HI_NB_DEVICES > 1
#include <rtems/rtems_bsdnet.h>
#include <bsp.h>
int rtems_bsdnet_loopattach(struct rtems_bsdnet_ifconfig*, int);

static struct rtems_bsdnet_ifconfig loopback_config =
   {"lo0", rtems_bsdnet_loopattach,	NULL, "127.0.0.1", "255.0.0.0", };
#undef RTEMS_BSP_NETWORK_DRIVER_NAME
#undef RTEMS_BSP_NETWORK_DRIVER_ATTACH
#define RTEMS_BSP_NETWORK_DRIVER_NAME    "ne1"
#define RTEMS_BSP_NETWORK_DRIVER_ATTACH  rtems_ne_driver_attach

struct rtems_bsdnet_ifconfig netdriver_config =
   {RTEMS_BSP_NETWORK_DRIVER_NAME,RTEMS_BSP_NETWORK_DRIVER_ATTACH,
	&loopback_config,"192.168.0.1","255.255.255.0",
   (char[]){ 0x00, 0x1F, 0xC6, 0xBF, 0x74, 0x06},
	0,0,0,0,0,9};

struct rtems_bsdnet_config rtems_bsdnet_config =
   {&netdriver_config,NULL,0,256 * 1024,256 * 1024,};

#endif /*(defined (X86_RTEMS) */

#endif /* __COMMON_H__ */
