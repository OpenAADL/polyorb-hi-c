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
   #define CONFIGURE_APPLICATION_NEEDS_TIMER_DRIVER
   #define CONFIGURE_MAXIMUM_POSIX_TIMERS          40
   #define CONFIGURE_MAXIMUM_TIMERS                40
   #define CONFIGURE_EXECUTIVE_RAM_SIZE    (512*1024)
   #define CONFIGURE_MAXIMUM_SEMAPHORES    20
   #define CONFIGURE_MAXIMUM_TASKS         20
   #define CONFIGURE_LIBIO_MAXIMUM_FILE_DESCRIPTORS 20


   int POSIX_Init ();
   #define CONFIGURE_MAXIMUM_POSIX_THREADS              __PO_HI_NB_TASKS + 10
   #define CONFIGURE_EXTRA_TASK_STACKS         (20 * RTEMS_MINIMUM_STACK_SIZE)
#ifdef __PO_HI_NB_PORTS
   #define CONFIGURE_MAXIMUM_POSIX_MUTEXES              __PO_HI_NB_TASKS + 10 + __PO_HI_NB_PORTS
   #define CONFIGURE_MAXIMUM_POSIX_CONDITION_VARIABLES  __PO_HI_NB_TASKS + 10 + __PO_HI_NB_PORTS
#else
   #define CONFIGURE_MAXIMUM_POSIX_MUTEXES              __PO_HI_NB_TASKS + 10 + __PO_HI_NB_PORTS
   #define CONFIGURE_MAXIMUM_POSIX_CONDITION_VARIABLES  __PO_HI_NB_TASKS + 10 + __PO_HI_NB_PORTS
#endif
   #define CONFIGURE_POSIX_INIT_THREAD_TABLE
   #define CONFIGURE_USE_IMFS_AS_BASE_FILESYSTEM
//   #include <po_hi_rtemsconfig.h>
   #include <rtems/confdefs.h>
#endif  /* RTEMS_POSIX */


#if defined (X86_RTEMS)
#include <rtems/rtems_bsdnet.h>

#include <bsp.h>
/*
 * Loopback interface
 */
int rtems_bsdnet_loopattach(struct rtems_bsdnet_ifconfig*, int);

static struct rtems_bsdnet_ifconfig loopback_config = {
	"lo0",				/* name */
	rtems_bsdnet_loopattach,	/* attach function */

	NULL,				/* link to next interface */

	"127.0.0.1",			/* IP address */
	"255.0.0.0",			/* IP net mask */
};

/*
 * Default network interface
 */
#define RTEMS_BSP_NETWORK_DRIVER_NAME    "ne1"
#define RTEMS_BSP_NETWORK_DRIVER_ATTACH  rtems_ne_driver_attach


struct rtems_bsdnet_ifconfig netdriver_config = {
	RTEMS_BSP_NETWORK_DRIVER_NAME,		/* name */
	RTEMS_BSP_NETWORK_DRIVER_ATTACH,	/* attach function */

	&loopback_config,		/* link to next interface */

	"10.0.2.5",			/* IP address */
	"255.255.255.0",		/* IP net mask */

	NULL,                           /* Driver supplies hardware address */
	0,				/* Use default driver parameters */
	0, /* mtu */
	0, /* rbuf_count */
	0, /* xbuf_count */
	0, /* port */
	9 /* irq */
};

/*
 * Network configuration
 */
struct rtems_bsdnet_config rtems_bsdnet_config = {
	&netdriver_config,

	NULL,

	0,			/* Default network task priority */
	256 * 1024,			/* Default mbuf capacity */
	256 * 1024,			/* Default mbuf cluster capacity */
};

#endif /*(defined (X86_RTEMS) &&  defined (NEED_TRANSPORT)) */



#endif /* __COMMON_H__ */
