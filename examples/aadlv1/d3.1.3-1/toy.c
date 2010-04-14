#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

void compute_during_1ms (int);

void compute_during_1ms (int n)
{
  /* XXX: How can this be accurate ? change with hartstone for instance */
  uint32_t b;
  for (b=0;b<0x8FFFF8;b++)
  {
    /*    printf("");*/
    fflush(stdout);
  }
}

int gnc_welcome = 1;
int tmtc_welcome = 1;

void user_read (int* value)
{
  printf ("Value: %d\n", *value);
}

void user_update (int* value)
{
  int v = *value;
  v++;
  *value = v;
  printf ("Value Updated: %d\n", *value);
}

void user_gnc_job()
{
  printf ("Begin computing : GNC\n");
  compute_during_1ms (600);
  printf ("End Computing : GNC\n");
}

void user_tmtc_job()
{
  printf ("Begin computing : GNC\n");
  compute_during_1ms (600);
  printf ("End Computing : GNC\n");
}

void user_gnc_identity ()
{
  if (gnc_welcome == 1)
    {
      printf ("Welcome GNC\n");
      gnc_welcome = 0;
    }
  else
    {
      printf ("Good by GNC\n");
      gnc_welcome = 1;
    }
}

void user_tmtc_identity ()
{
  if (tmtc_welcome == 1)
    {
      printf ("Welcome TMTC\n");
      tmtc_welcome = 0;
    }
  else
    {
      printf ("Good bye TMTC\n");
      tmtc_welcome = 1;
    }
}
