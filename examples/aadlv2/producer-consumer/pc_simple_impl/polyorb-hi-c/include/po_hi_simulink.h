/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2007-2009 Telecom ParisTech, 2010-2014 ESA & ISAE.
 */

#ifndef  __PO_HI_SIMULINK_H__
#define  __PO_HI_SIMULINK_H__

#include <stdio.h>
#include <deployment.h>
#include <string.h>
#include <types.h>
#include <rtwtypes.h>
#include <rtmodel.h>
#include <rt_sim.h>
#include <rt_logging.h>
#ifdef UseMMIDataLogging
#include <rt_logging_mmi.h>
#endif
#include <rt_nonfinite.h>


extern void MdlInitializeSizes(void);
extern void MdlInitializeSampleTimes(void);
extern void MdlStart(void);
extern void MdlOutputs(int_T tid);
extern void MdlUpdate(int_T tid);
extern void MdlTerminate(void);




void* __po_hi_simulink_find_signal (const char* name);
void* __po_hi_simulink_find_var (const char* name);
void* __po_hi_simulink_find_parameter (const char* name);
void __po_hi_simulink_init (void);

void __po_hi_simulink_update (void);

#endif /* __PO_HI_SIMULINK_H__ */
