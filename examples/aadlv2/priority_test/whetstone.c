/*
 * whetstone.c : adaptation of the Whetstone benchmark
 * from Curnow, H.J. and Wichman, B.A. "A Synthetic Benchmark"
 * Computer Journal, Volume 19, Issue 1, February 1976., p. 43-49.
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <po_hi_time.h>
#include <unistd.h>
#include <math.h>

/*Values from the original Algol Whetstone program
  and the Pascal SmallWhetstone program*/
double T = 0.499975;
double T1 = 0.50025;
double T2 =  2.0;

double LOOP = 1.0;
int N8 = 10;
int N9 = 7;

double Value = 0.941377; // Value calculated in main loop
double Tolerance = 0.00001; // Determined by interval arithmetic

double KIPS;

//Interger constant
int I;
int IJ = 1;
int IK = 2;
int IL = 3;

//double
double Y = 1.0;
double Z;
double sum = 0; // Accumulates value of Z

/* Functions initialization */
void CA (double * array, int I);
void P0 (void);
void P3 (double X, double Y, double * Z);
void burnproc(int loop);

void burnproc(int loop)
{
  //Temporal Variable
  __po_hi_time_t  tstart;
  __po_hi_time_t  tfin;
  int i, j, r;

  double * E1;
  E1 = (double *)malloc(N9 * sizeof (double));

  // Start benchmark timing at this point.

  int test1 = __po_hi_get_time(&tstart);
  if (test1 < 0)
    { printf("ERROR TIME 1");
      fflush (stdout);}

  //Main Loop
  for (j=0; j<loop ;j++){

    //Initializing the array.

    for (r = 0 ; r < N9 ; r++)
      {
	E1[r] = 0.0;
      }

    //Module 6 : Interger Arithmetic
    IJ = (IK - IJ) * (IL - IK);
    IK = IL - (IK - IJ);
    IL = (IL - IK) * (IK + IL);

    E1[(IL - 1)] = (double)(IJ + IK + IL);
    E1[(IK - 1)] = sin((double)IL);

    //Module 8: Procedure Calls
    Z = E1[4];
    for (i = 0; i < N8;){
      i++;
      P3(Y * (double)i , Y + Z, &Z);
    }

    //Second version of Module 6:
    IJ = IL - (IL - 3) * IK;
    IL = (IL - IK) * (IK - IJ);
    IK = (IL - IK) * IK;

    E1[(IL - 1)] = (double)(IJ + IK + IL);
    E1[(IK + 1)] = fabs( cos(Z) );

    //Module 9 Array References
    I = 1;
    while( I <= N9){
      //P0
      E1[IJ] = E1[IK];
      E1[IK] = E1[IL];
      E1[IL] = E1[IJ];
      I++;
    }

    //Module 11: Standard Mathematical Functions
    Z = sqrt( exp( log(E1[(N9 - 1)]) /T1) );
    sum = sum + Z;

    //Check the current value of the loop computation
    /* if (fabs(Z - Value) > Tolerance)
       {
       sum = 2.0 * sum; // Force error at end
       IJ = IJ +1; // Prévents optimization
       }*/
  }

  //Self-validation check
  /*
  if( fabs(sum/((double)loop) - Value) > (Tolerance*(double)loop ) )
     {
       printf("Workload Failure");
       fflush (stdout);
     }
  */

  /*     Stop benchmark timing at this point.  */

  int test2 = __po_hi_get_time(&tfin);
  if (test2 < 0)
    { printf("ERROR TIME 2");
      fflush (stdout);}

  /*
    ----------------------------------------------------------------
    Performance in Whetstone KIP's per second is given by

    (100*LOOP*loop)/TIME

    where TIME is in seconds.
    --------------------------------------------------------------------
  */

#ifdef WHETSTONE_DEBUG

  float duration = (float)(tfin.sec - tstart.sec)+((float)((tfin.nsec-tstart.nsec))/1000000000.0);
  printf("Time duration :%f sec.\n------------------------\n",duration);
  fflush (stdout);

  if (duration <= 0.0) {
    printf("Insufficient duration- Increase the LOOP count\n");
  }
  else
    {
      printf("Loops: %f, Iterations: %d.\n",
             LOOP, loop, duration);
      fflush (stdout);
      printf("------------------------\n");
      fflush (stdout);

      KIPS = (100.0*LOOP*(float)loop)/(float)(duration);

      if (KIPS >= 1000.0)
        {printf("C Converted Double Precision Whetstones: %.1f MIPS\n", KIPS/1000.0);
          fflush (stdout);}
      else
        {printf("C Converted Double Precision Whetstones: %.1f KIPS\n", KIPS);
      fflush (stdout);}
    }
  printf("---------------------------\n");
  fflush (stdout);
  printf("---------------------------\n");
  fflush (stdout);
#endif /* WHETSTONE_DEBUG */

  free (E1);
}

void P3 (double X, double Y, double * Z){

  double Xtemp, Ytemp;
  Xtemp = (*Z + X) * T;
  Ytemp = (Xtemp + Y) * T;

  *Z = (Xtemp + Ytemp)/T2;
}
