/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2007-2009 Telecom ParisTech, 2010-2017 ESA & ISAE.
 */



#include <po_hi_config.h>
#include <po_hi_returns.h>
#include <po_hi_debug.h>
#include <po_hi_task.h>
#include <po_hi_types.h>
#include <po_hi_utils.h>
#include <po_hi_semaphore.h>

#include <deployment.h>


//#ifndef __PO_HI_NB_PROTECTED
//#define __PO_HI_NB_PROTECTED 0
//#endif

#if defined (RTEMS_POSIX) || defined (POSIX) || defined (XENO_POSIX)
#define __USE_UNIX98 1
#include <pthread.h>
#include <semaphore.h>
//#include <sys/sem.h>
#endif

#ifdef XENO_NATIVE
#include <native/mutex.h>
#endif

#ifdef __PO_HI_RTEMS_CLASSIC_API
#include <rtems.h>
#endif

