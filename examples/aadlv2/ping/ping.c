#include <stdio.h>

int p=0;

void user_do_ping_spg (int *v)
{
#ifdef MULTIPLE_BUSES
#include <deployment.h>
   if ( ( p % 2 ) == 0)
   {
      __po_hi_transport_associate_port_bus (ping_me_global_data_sink, bus_first_bus);
   }
   else
   {
      __po_hi_transport_associate_port_bus (ping_me_global_data_sink, bus_second_bus);
   }
#endif
  printf ("*** SENDING PING *** %d\n", p);
  *v=p;
  p++;
  fflush (stdout);
}

void user_ping_spg (int i)
{
  printf ("*** PING *** %d\n" ,i);
  fflush (stdout);
}

void recover (void)
{
  printf ("*** RECOVER ACTION ***\n");
  fflush (stdout);
}
