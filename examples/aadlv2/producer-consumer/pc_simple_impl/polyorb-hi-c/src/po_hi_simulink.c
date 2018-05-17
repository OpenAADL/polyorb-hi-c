/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2007-2009 Telecom ParisTech, 2010-2014 ESA & ISAE.
 */

#include <po_hi_config.h>
#include <po_hi_simulink.h>
#include <deployment.h>
#include <ext_work.h> /* from Simulink */
#include <po_hi_debug.h>

/*
static struct {
   int    stopExecutionFlag;
   int    isrOverrun;
   int    overrunFlags[NUMST];
   int    eventFlags[NUMST];
   const    char *errmsg;
} GBLbuf;
*/

extern __PO_HI_SIMULINK_MODEL_TYPE *MODEL(void);

__PO_HI_SIMULINK_MODEL_TYPE rtmodel;

#if NCSTATES > 0
extern void rt_ODECreateIntegrationData(RTWSolverInfo *si);
extern void rt_ODEUpdateContinuousStates(RTWSolverInfo *si);

#define rt_CreateIntegrationData(S) \
   rt_ODECreateIntegrationData(rtmGetRTWSolverInfo(S));
#define rt_UpdateContinuousStates(S) \
   rt_ODEUpdateContinuousStates(rtmGetRTWSolverInfo(S));
#else
#define rt_CreateIntegrationData(S)  \
   rtsiSetSolverName(rtmGetRTWSolverInfo(S),"FixedStepDiscrete");
#define rt_UpdateContinuousStates(S) /* Do Nothing */
#endif


#ifdef EXT_MODE
#  define rtExtModeSingleTaskUpload(S)                          \
{                                                            \
   int stIdx;                                              \
   rtExtModeUploadCheckTrigger(rtmGetNumSampleTimes(S));   \
   for (stIdx=0; stIdx<NUMST; stIdx++) {                   \
      if (rtmIsSampleHit(S, stIdx, 0 /*unused*/)) {       \
         rtExtModeUpload(stIdx,rtmGetTaskTime(S,stIdx)); \
      }                                                   \
   }                                                       \
}
#else
#  define rtExtModeSingleTaskUpload(S) /* Do nothing */
#endif




void __po_hi_simulink_init (void)
{
   __PO_HI_SIMULINK_MODEL_TYPE *S;
       rt_InitInfAndNaN(sizeof(real_T));


   S = MODEL();

   MdlInitializeSizes();
   MdlInitializeSampleTimes();

   rt_SimInitTimingEngine (rtmGetNumSampleTimes(S),
         rtmGetStepSize(S),
         rtmGetSampleTimePtr(S),
         rtmGetOffsetTimePtr(S),
         rtmGetSampleHitPtr(S),
         rtmGetSampleTimeTaskIDPtr(S),
         rtmGetTStart(S),
         &rtmGetSimTimeStep(S),
         &rtmGetTimingData(S));

   rt_CreateIntegrationData(S);

#ifdef UseMMIDataLogging
   rt_FillStateSigInfoFromMMI(rtmGetRTWLogInfo(S),&rtmGetErrorStatus(S));
   rt_FillSigLogInfoFromMMI(rtmGetRTWLogInfo(S),&rtmGetErrorStatus(S));
#endif
   rt_StartDataLogging(rtmGetRTWLogInfo(S),
         rtmGetTFinal(S),
         rtmGetStepSize(S),
         &rtmGetErrorStatus(S));

   rtExtModeCheckInit(rtmGetNumSampleTimes(S));
   rtExtModeWaitForStartPkt(rtmGetRTWExtModeInfo(S),
         rtmGetNumSampleTimes(S),
         (boolean_T *)&rtmGetStopRequested(S));

   MdlStart();
}


void __po_hi_simulink_update (void)
{
   real_T tnext;


   rtExtModeOneStep(rtmGetRTWExtModeInfo((&rtmodel)),
         rtmGetNum(&rtmodel)ampleTime(&rtmodel)((&rtmodel)),
         (boolean_T *)&rtmGet(&rtmodel)topReque(&rtmodel)ted((&rtmodel)));

       tnext = rt_SimGetNextSampleHit();
           rtsiSetSolverStopTime(rtmGetRTWSolverInfo(&rtmodel),tnext);


   MdlOutputs(0);

    rtExtModeSingleTaskUpload(&rtmodel);

   MdlUpdate(0);
   rt_SimUpdateDiscreteTaskSampleHits(rtmGetNumSampleTimes(&rtmodel),
         rtmGetTimingData(&rtmodel),
         rtmGetSampleHitPtr(&rtmodel),
         rtmGetTPtr(&rtmodel));

   if (rtmGetSampleTime(&rtmodel,0) == CONTINUOUS_SAMPLE_TIME) {
      rt_UpdateContinuousStates(&rtmodel);
   }
   rtExtModeCheckEndTrigger();

}
