/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://assert-project.net/taste
 *
 * Copyright (C) 2007-2009 Telecom ParisTech, 2010-2012 ESA & ISAE.
 */

/* Needs to include time.h for Frama-C, as we are using po_hi_time.h
 * that does define a function using clockid_t
 */
#ifndef HAVE_CLOCK_GETTIME
#if defined (__CYGWIN__) || defined (__MINGW32__)
#else
#include <xlocale.h>
#endif

#include <time.h>
#endif

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

void __po_hi_copy_array_uint8 (__po_hi_uint8_t* dst, __po_hi_uint8_t* src, __po_hi_uint16_t size)
{
  memcpy (dst, src, size);
}
