#include <stdio.h>

void user_ping_spg (int i)
{
  printf ("*** PING *** %d\n" ,i);
  fflush (stdout);
}
/* redundant
void recover (void)
{
  printf ("*** RECOVER ACTION ***\n");
  fflush (stdout);
}*/
