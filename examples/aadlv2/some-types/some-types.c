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
  fflush (stdout); 
}

void user_receive_boolean (int boolean)
{
  printf ("Receiving boolean : %d\n", boolean);
  fflush (stdout); 
}

void user_emit_integer (int* integer)
{
  integer_type_var++;
  *integer = integer_type_var;
  printf ("Emetting integer : %d\n", *integer);
  fflush (stdout); 
}

void user_emit_array (software__array_type* data_source)
{
  int i;
  for (i = 0; i < 16; i++)
    {
      (*data_source)[i]=i;
    }
  
}

void user_emit_bounded_array (software__bounded_array_type* data_source)
{
  int i;
  for (i = 0; i < 16; i++)
    (*data_source).data[i]=i;
  data_source->length = 16;

  printf ("Emetting bounded array\n");
  printf ("\n");
  fflush (stdout); 
}

void user_receive_integer (int integer)
{
  printf ("Receiving integer : %d\n", integer);
  fflush (stdout); 
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

  printf ("\n");
  fflush(stdout);
}

void user_receive_bounded_array (software__bounded_array_type data)
{
  int i;
  printf("Receive bounded array: %d", data.length);
  fflush (stdout);
  for (i = 0; i < data.length; i++)
    assert (data.data[i] == i);

  printf (" OK \n");
  fflush(stdout);
}
