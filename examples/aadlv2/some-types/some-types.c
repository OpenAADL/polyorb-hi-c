/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2017 ESA & ISAE.
 */

#include <assert.h>
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

void user_emit_integer (int* integer)
{
  integer_type_var++;
  *integer = integer_type_var;
  printf ("Emetting integer : %d\n", *integer);
}

void user_emit_array (software__array_type* data_source)
{
  int i;
  for (i = 0; i < 16384; i++)
    (*data_source)[i]=i;

  printf ("Emetting array\n");
  printf ("\n");
}

void user_receive_integer (int integer)
{
  printf ("Receiving integer : %d\n", integer);
}

void user_emit_struct (software__struct_type_impl *v)
{
  static int i = 0;
  software__struct_type_impl value;

  value.x = i;
  value.y = i;

  printf ("*** SENDING PING *** %d\n", i);
  i++;
  *v = value;
  fflush (stdout);
}

void user_receive_struct (software__struct_type_impl i)
{
  printf ("*** PING *** (%d, %d)\n" ,i.x, i.y);
  fflush (stdout);
}

void user_receive_array (software__array_type data)
{
  int i;
  printf("Receive array: ");
  for (i = 0; i < 16; i++)
    assert (data[i] == i);

  printf (" OK \n");
  fflush(stdout);
}
