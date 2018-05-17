/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2012-2014 ESA & ISAE.
 */

#ifndef __PO_HI_DRIVERS_RTEMS_UTILS_H__
#define __PO_HI_DRIVERS_RTEMS_UTILS_H__

#include <po_hi_debug.h>

#define __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(fd,num,arg) \
        { int ioctl_ret ; \
        if ( (ioctl_ret=ioctl(fd,num,arg)) != RTEMS_SUCCESSFUL ) { \
                        __PO_HI_DEBUG_DEBUG("[RTEMS UTILS] IOCTL " #num " failed: ret: %d \n",ioctl_ret); \
                } \
  }

#endif
