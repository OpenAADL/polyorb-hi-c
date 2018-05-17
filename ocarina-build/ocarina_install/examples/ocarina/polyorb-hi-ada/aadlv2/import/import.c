#include <stdio.h>

typedef int simple_type;
typedef simple_type array_type_i[4];

extern int array_type_i__length (array_type_i a);

void ping_spg (array_type_i a)
{
  int i;
  int l = array_type_i__length (a);

  printf ("* C PING (");

  for (i = 0; i < l; i++) {
    printf ("%d", a[i]);

    if (i < l - 1) {
      printf (", ");
    }
  }

  printf (") *\n");
  fflush (stdout);
}
