/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2008, GET-Telecom Paris.
 */

#include <po_hi_config.h>
#include <po_hi_types.h>
#include <po_hi_debug.h>
#include <po_hi_returns.h>
/* Header files in PolyORB-HI */

#include <types.h>	
/* Header files from generated code */

#include <string.h>

void __po_hi_copy_array (void* dst, void* src, __po_hi_uint16_t size)
{
   memcpy (dst, src, size);
}
