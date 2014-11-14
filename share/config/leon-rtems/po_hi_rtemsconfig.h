/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2008-2009 Telecom ParisTech, 2010-2014 ESA & ISAE.
 */

#include <deployment.h>

#define CONFIGURE_LIBIO_MAXIMUM_FILE_DESCRIPTORS 32

#if (defined (__PO_HI_NEED_DRIVER_SPACEWIRE_RASTA)) ||  \
    (defined (__PO_HI_NEED_DRIVER_SERIAL_RASTA)) || \
    (defined (__PO_HI_USE_GPROF)) || \
    (defined (__PO_HI_NEED_DRIVER_SERIAL_LEON)) || \
    (defined (__PO_HI_NEED_DRIVER_SERIAL_LEON_SENDER)) || \
    (defined (__PO_HI_NEED_DRIVER_SERIAL_LEON_RECEIVER)) || \
    (defined (__PO_HI_NEED_DRIVER_1553_RASTA))
#define CONFIGURE_MAXIMUM_DRIVERS 16
#endif
