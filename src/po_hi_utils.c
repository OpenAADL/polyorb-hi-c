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
#include <po_hi_time.h>
#include <po_hi_types.h>
#include <po_hi_debug.h>
#include <po_hi_utils.h>
/* Header files in PolyORB-HI */

#include <deployment.h>
/* Header files from generated code */

#include <stdlib.h>

#if defined(__PO_HI_USE_VCD) && defined(__unix__)
enum tagVCD VCD_state = VCD_UNCHECKED;
#endif

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

#ifdef __PO_HI_USE_VCD
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <pthread.h>
#include <fcntl.h>
#include <time.h>

#include <po_hi_returns.h>

#include <deployment.h>

int                     __po_hi_vcd_file;
int                     __po_hi_vcd_init = 0;
__po_hi_time_t          __po_hi_vcd_start_time;
pthread_mutex_t         __po_hi_vcd_mutex;
pthread_mutexattr_t     __po_hi_vcd_mutex_attr;

#if __PO_HI_NB_PORTS > 0
extern __po_hi_int8_t*        __po_hi_gqueues_sizes[__PO_HI_NB_TASKS];
extern __po_hi_uint8_t*       __po_hi_gqueues_used_size[__PO_HI_NB_TASKS];
extern __po_hi_int8_t         __po_hi_gqueues_nb_ports[__PO_HI_NB_TASKS];
#endif

void __po_hi_instrumentation_vcd_init ()
{
#if __PO_HI_NB_PORTS > 0
   int                     port, task;
#endif

   int i;
   char                    buf[1024];
   int                     size_to_write = 0;
   time_t                  current_time;

#if defined(__PO_HI_USE_VCD) && defined(__unix__)
   if (VCD_state == VCD_UNCHECKED)
   {
          VCD_state = NULL == getenv("VCD_ENABLED")?VCD_DISABLED:VCD_ENABLED;
   }

   if (VCD_state != VCD_ENABLED)
   {
       return;
   }
#endif

   if (__po_hi_vcd_init == 0)
   {
      __po_hi_vcd_init = 1;
      pthread_mutexattr_init (&__po_hi_vcd_mutex_attr);
      pthread_mutex_init (&__po_hi_vcd_mutex, &__po_hi_vcd_mutex_attr);

      pthread_mutex_lock (&__po_hi_vcd_mutex);
      if (__po_hi_get_time(&__po_hi_vcd_start_time) != __PO_HI_SUCCESS)
      {
         __DEBUGMSG("[POHIC-INSTRUMENTATION] Could not get time\n");
      }
      __po_hi_vcd_file = open ("bench.vcd", O_WRONLY|O_CREAT|O_SYNC, S_IRUSR|S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH);
      if (__po_hi_vcd_file > 0)
      {
         write (__po_hi_vcd_file, "$date\n", 6);

         memset (buf, '\0', 1024);
         time (&current_time);
         size_to_write = sprintf (buf, "%s", ctime(&current_time));
         write (__po_hi_vcd_file, buf, size_to_write);

         write (__po_hi_vcd_file, "$end\n", 5);
         write (__po_hi_vcd_file, "$version\n", 9);
         write (__po_hi_vcd_file, "VCD generator tool version info text.\n", 38);
         write (__po_hi_vcd_file, "$end\n", 5);
         write (__po_hi_vcd_file, "$comment\n", 9);
         write (__po_hi_vcd_file, "This file has been create by polyorb-hi-c runtime of ocarina.\n", 62);
         write (__po_hi_vcd_file, "$end\n", 5);
         write (__po_hi_vcd_file, "$timescale 1us $end\n", 20);
         write (__po_hi_vcd_file, "$scope module tasks $end\n", 25);
         for (i = 0 ; i < __PO_HI_NB_TASKS ; i++) \
         { \
            memset (buf, '\0', 1024);
            size_to_write = sprintf (buf, "$var wire 1 t%d task_%d $end\n", i, i);
            write (__po_hi_vcd_file, buf, size_to_write);
         } \
         write (__po_hi_vcd_file, "$upscope $end\n", 14);
#if __PO_HI_NB_PROTECTED > 0
         write (__po_hi_vcd_file, "$scope module mutexes $end\n", 27 );
         for (i = 0; i < __PO_HI_NB_PROTECTED; ++i)
         { \
            memset (buf, '\0', 1024);
            size_to_write = sprintf (buf, "$var wire 1 w%i awaited_%i $end\n", i, i);
            write (__po_hi_vcd_file, buf, size_to_write);
         } \
         for (i = 0; i < __PO_HI_NB_PROTECTED; ++i)
         {
            memset (buf, '\0', 1024);
            size_to_write = sprintf (buf, "$var wire 1 l%i locked_%i $end\n", i, i);
            write (__po_hi_vcd_file, buf, size_to_write);
         }
         write (__po_hi_vcd_file, "$upscope $end\n", 14);
#endif
#if __PO_HI_NB_PORTS > 0
         write (__po_hi_vcd_file, "$scope module ports $end\n", 25);
         for (task = 0; task < __PO_HI_NB_TASKS; task++)
         {
            for (port = 0; port < __po_hi_gqueues_nb_ports[task]; port++)
            {

               if (__po_hi_gqueues_sizes[task][port] > 0)
               {

                  memset (buf, '\0', 1024);
                  size_to_write = sprintf (buf, "$var real %i p%i.%i port_%i_%i $end\n", __po_hi_gqueues_sizes[task][port], task, port, task, port);
                  write (__po_hi_vcd_file, buf, size_to_write);
               }
            }
         }
         write (__po_hi_vcd_file, "$upscope $end\n", 14);
#endif
         write (__po_hi_vcd_file, "$enddefinitions $end\n", 21);
         write (__po_hi_vcd_file, "$dumpvars\n", 10);
         for (i = 0 ; i < __PO_HI_NB_TASKS ; i++)
         {
            memset (buf, '\0', 1024);
            size_to_write = sprintf (buf, "0t%d\n", i);
            write (__po_hi_vcd_file, buf, size_to_write);
         }
#if __PO_HI_NB_PROTECTED > 0
         for (i = 0; i < __PO_HI_NB_PROTECTED; ++i)
         {
            memset (buf, '\0', 1024);
            size_to_write = sprintf (buf, "0w%d\n", i);
            write (__po_hi_vcd_file, buf, size_to_write);
         }
         for (i = 0; i < __PO_HI_NB_PROTECTED; ++i)
         {
            memset (buf, '\0', 1024);
            size_to_write = sprintf (buf, "0l%d\n", i);
            write (__po_hi_vcd_file, buf, size_to_write);
         }
#endif
#if __PO_HI_NB_PORTS > 0
         for (task = 0; task < __PO_HI_NB_TASKS; ++task)
         {
            for (port = 0; port < __po_hi_gqueues_nb_ports[task]; ++port)
            {
               if (__po_hi_gqueues_sizes[task][port] > 0)
               {
                  memset (buf, '\0', 1024);
                  size_to_write = sprintf (buf, "r0 p%d.%d\n", task, port);
                  write (__po_hi_vcd_file, buf, size_to_write);
               }
            }
         }
#endif
      write (__po_hi_vcd_file, "$end\n", 5);

      pthread_mutex_unlock (&__po_hi_vcd_mutex);
      }
      else
      {
         __DEBUGMSG("[POHIC-INSTRUMENTATION] Could not create file !\n");
      }
   }
}
#endif
