#include <stdio.h>

void user_hello_spg_1 (void)
{
#if 1
        printf ("FIRST TASK\n");
        fflush (stdout);
#endif
}

void user_hello_spg_2 (void)
{
#if 1
        printf ("SECOND TASK\n");
        fflush (stdout);
#endif
}
