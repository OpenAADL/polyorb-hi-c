#include <stdio.h>
#include <stdint.h>

int16_t boolean_type_var = 0;
int32_t integer_type_var = 0;

void user_emit_boolean( int16_t* boolean)
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

void user_receive_boolean (int16_t boolean)
{
  printf ("Receiving boolean : %d\n", boolean);
}

void user_emit_integer( int32_t* integer)
{
  integer_type_var++;
  *integer = integer_type_var;
  printf ("Emetting integer : %d\n", *integer);
}

void user_receive_integer (int32_t integer)
{
  printf ("Receiving integer : %d\n", integer);
}
