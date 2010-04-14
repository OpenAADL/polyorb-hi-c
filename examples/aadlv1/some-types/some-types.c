#include <stdio.h>
#include <types.h>

int boolean_type_var = 0;
int integer_type_var = 0;

void user_emit_boolean( int* boolean)
{
  if (boolean_type_var == 1)
    {
      boolean_type_var = 0;
    }
  else
    {
      boolean_type_var = 1;
    }
  *boolean = boolean_type_var;
  printf ("Sending boolean : %d\n", *boolean);
}

void user_receive_boolean (int boolean)
{
  printf ("Receiving boolean : %d\n", boolean);
}

void user_emit_integer( int* integer)
{
  integer_type_var++;
  *integer = integer_type_var;
  printf ("Emetting integer : %d\n", *integer);
}

void user_receive_integer (int integer)
{
  printf ("Receiving integer : %d\n", integer);
}

void user_emit_struct (struct_type_impl *v)
{
  static int i = 0;
  struct_type_impl value;

  value.x = i;
  value.y = i;
  
  printf ("*** SENDING PING *** (%d, %d)\n", value.x, value.y);
  i++;
  *v = value;
  fflush (stdout);
}

void user_receive_struct (struct_type_impl i)
{
  printf ("*** PING *** (%d, %d)\n" ,i.x, i.y);
  fflush (stdout);
}
