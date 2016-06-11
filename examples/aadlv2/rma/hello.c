/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2016 ESA & ISAE.
 */

#include <stdio.h>
#include <po_hi_time.h>

void user_hello_spg_1 (void)
{
#if 1
  printf ("[%d] FIRST TASK\n", milliseconds_since_epoch());
  fflush (stdout);
#endif
}

void user_hello_spg_2 (void)
{
#if 1
  printf ("[%d] SECOND TASK\n", milliseconds_since_epoch());
  fflush (stdout);
#endif
}
