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
#include <po_hi_types.h>
#include <po_hi_debug.h>
#include <po_hi_returns.h>
/* Header files in PolyORB-HI */

#include <types.h>
/* Header files from generated code */

#include <string.h>

void __po_hi_copy_array (void* dst, void* src, __po_hi_uint32_t size)
{
   memcpy (dst, src, size);
}
