#include <stdio.h>
#include <po_hi_monitor.h>


void user_produce_pkts ()
{
  static int p = 0;
  printf ("*** PRODUCE PKT WITH VALUE *** %d\n", p);
  p++;
  fflush (stdout);
}


void user_do_ping_spg ()
{
  printf ("*** SENDING PKT *** \n");
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
