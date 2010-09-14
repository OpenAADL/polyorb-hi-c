/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2010, European Space Agency (ESA).
 */

#ifndef __PO_HI_DEBUG_H__

#include <po_hi_config.h>
#include <po_hi_time.h>

#ifdef __PO_HI_DEBUG
#include <stdio.h>
#define __DEBUGMSG(s, args...) fprintf(stderr, s, ##args); fflush (stderr); 
#else
#define __DEBUGMSG(s, args...) 
#endif

#endif	/* __DEBUG_H__ */
