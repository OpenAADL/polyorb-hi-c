#include <stdio.h>
#include <types.h>

void ping_spg (software__simple_type s)
{
  printf ("* C PING: %d\n", s);
  fflush (stdout);
}
