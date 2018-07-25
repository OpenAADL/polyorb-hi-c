
#include <stdio.h>
#include <po_hi_time.h>
#include <unistd.h>

#include "whetstone.c"

#define loop 167

void task_1 (void)
{
  // Time variable, C = WCET/100
  int32_t C1 = 2 ;
  int i = 0;

  //Temporal Variable
  __po_hi_time_t  tstart;
  __po_hi_time_t  tfin;

  printf("Starting FIRST TASK...\n");
  fflush (stdout);

  //Starting Time
  int test1 = __po_hi_get_time(&tstart);
  if (test1 < 0)
    {
      printf("ERROR TIME 1");
      fflush (stdout);
    }

  //Executute Task with a certain duration

  for (i=0 ; i < C1 ; i++){burnproc(loop);}

  //Ending Time
  int test2 = __po_hi_get_time(&tfin);
  if (test2 < 0)
    { printf("ERROR TIME 2");
      fflush (stdout);}

  //Compute Time Duration
  float duration = 1000.0*((float)(tfin.sec - tstart.sec)+((float)((tfin.nsec-tstart.nsec))/1000000000.0));
  printf ("[%f msec] Completed FIRST TASK.\n",duration);
  fflush (stdout);

}

void task_2 (void)
{
  // Time variable, C = WCET/100
  int32_t C2 = 1;
  int i = 0;

  //Temporal Variable
  __po_hi_time_t  tstart;
  __po_hi_time_t  tfin;

  printf("Starting SECOND TASK...\n");
  fflush (stdout);

  //Starting Time
  int test1 = __po_hi_get_time(&tstart);
  if (test1 < 0)
    { printf("ERROR TIME 1");
      fflush (stdout);}

  //Executute Task with a certain duration

  for (i=0 ; i < C2 ; i++){burnproc(loop);}

  //Ending Time
  int test2 = __po_hi_get_time(&tfin);
  if (test2 < 0)
    { printf("ERROR TIME 2");
     fflush (stdout);}

  //Compute Time Duration
  float duration = 1000.0*((float)(tfin.sec - tstart.sec)+((float)((tfin.nsec-tstart.nsec))/1000000000.0));
  printf ("[%f msec] Completed SECOND TASK.\n",duration);
  fflush (stdout);

}

void task_3 (void)
{

  //Temporal Variable
  __po_hi_time_t  tstart;
  __po_hi_time_t  tfin;

  // Time variable, C = WCET/100
  int32_t C3 = 2 ;
  int i = 0;

  printf("Starting THIRD TASK...\n");
  fflush (stdout);

  //Starting Time
  int test1 = __po_hi_get_time(&tstart);
  if (test1 < 0)
    { printf("ERROR TIME 1");
      fflush (stdout);}

  //Executute Task with a certain duration

  for (i=0 ; i < C3 ; i++){burnproc(loop);}

  //Ending Time
  int test2 = __po_hi_get_time(&tfin);
  if (test2 < 0)
    { printf("ERROR TIME 2");
     fflush (stdout);}

  //Compute Time Duration
  float duration = 1000.0*((float)(tfin.sec - tstart.sec)+((float)((tfin.nsec-tstart.nsec))/1000000000.0));
  printf ("[%f msec] Completed THIRD TASK.\n",duration);
  fflush (stdout);

}
