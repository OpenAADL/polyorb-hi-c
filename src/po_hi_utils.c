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
#include <po_hi_time.h>
#include <po_hi_types.h>
#include <po_hi_debug.h>
#include <po_hi_utils.h>
/* Header files in PolyORB-HI */

#include <deployment.h>	
/* Header files from generated code */

#include <stdlib.h>

int __po_hi_simulate_wcet (__po_hi_time_t time1, __po_hi_time_t time2)
{
#if defined (POSIX) || defined (RTEMS_POSIX)
   __po_hi_time_t tmp;
   __po_hi_time_t limit;
   __po_hi_get_time(&limit);
   limit = limit + time2;
   while (1)
   {
      __po_hi_get_time (&tmp);
      if (tmp >= limit)
      {
         return 0;
      }
   }
   return 0;
   /*
#else
   __DEBUGMSG ("WCET simulation not handled at this time\n");
   */
#endif
   return 0;
}


int __po_hi_compute_miss (__po_hi_uint8_t rate)
{
   int v;
   v = rand () % 100;
   
   if (v <= rate)
   {
      return 0;
   }
   
   return 1;
}


unsigned long __po_hi_swap_byte (unsigned long value)
{
   union u {unsigned long vi; unsigned char c[sizeof(unsigned long)];}; 
   union v {unsigned long ni; unsigned char d[sizeof(unsigned long)];};
   union u un; 
   union v vn; 
   un.vi = value;
   vn.d[0]=un.c[3]; 
   vn.d[1]=un.c[2]; 
   vn.d[2]=un.c[1]; 
   vn.d[3]=un.c[0]; 
   return (vn.ni); 
}


