#include <stdio.h>
#include <stdint.h>
#include <math.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>
#include <types.h>

int16_t boolean_type_var = 0;
int32_t integer_type_var = 0;
int64_t natural_type_var = 0;

int8_t int8_type_var = 0;
int16_t int16_type_var = 0;
int32_t int32_type_var = 0;
int64_t int64_type_var = 0;

uint8_t uint8_type_var = 0;
uint16_t uint16_type_var = 0;
uint32_t uint32_type_var = 0;
uint64_t uint64_type_var = 0;

float_t float0_type_var = 0.0;
float_t float32_type_var = 0.0;
double_t float64_type_var = 0.0;
char char_type_var = 'A';

/* Macros Definition */

/* Integer */

#define EMIT_TYPE_INT(TYPE, VAR, FORMAT)	\
  void user_emit_##TYPE (VAR * type);           \
  void user_emit_##TYPE (VAR * type)	\
  {\
    TYPE##_type_var++;          \
      *type = TYPE##_type_var;\
      printf("Emetting integer : ");\
      printf(FORMAT, *type);\
      printf("\n");	\
      fflush (stdout);        \
  }

#define RECEIVE_TYPE_INT(TYPE, VAR, FORMAT)		\
  void user_receive_##TYPE (VAR type);\
  void user_receive_##TYPE (VAR type) \
  {\
    printf("Receiving integer : ");\
    printf(FORMAT, type);\
    printf("\n");	\
    fflush (stdout);     \
  }

/* Float */

#define EMIT_TYPE_FLOAT(TYPE, VAR, FORMAT)	\
  void user_emit_##TYPE (VAR * type);           \
  void user_emit_##TYPE (VAR * type)            \
  {\
    TYPE##_type_var++;	\
      *type = TYPE##_type_var;\
      printf("Emetting float : ");\
      printf(FORMAT, *type);\
      printf("\n");	\
      fflush (stdout);    \
  }

#define RECEIVE_TYPE_FLOAT(TYPE, VAR, FORMAT)	\
  void user_receive_##TYPE (VAR type);          \
  void user_receive_##TYPE (VAR type)         \
  {\
  printf("Receiving float : ");\
    printf(FORMAT, type);\
    printf("\n");         \
    fflush (stdout);      \
  }


/* Boolean sub case */
void user_emit_boolean(int16_t* boolean);
void user_emit_boolean(int16_t* boolean)
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

void user_receive_boolean (int16_t boolean);
void user_receive_boolean (int16_t boolean)
{
  printf ("Receiving boolean : %d\n", boolean);
  fflush (stdout);
}


/* Char sub case */

void user_emit_char (char* character);
void user_emit_char (char* character)
{

  char_type_var =  'A' + ((char_type_var - 'A' +1) %26) ;
  *character = (char)char_type_var;

  printf ("Emetting char : %c\n", *character);
  fflush (stdout);
}

void user_receive_char (char character);
void user_receive_char (char character)
{
  printf ("Receiving char : %c\n", character);
  fflush (stdout);
}

/* Array sub case */

void user_emit_array (software__array_type* data);
void user_emit_array (software__array_type* data)
{
  int i;
  for (i = 0; i < 16; i++)
    {(*data)[i]=i;}
  printf ("Emetting array\n");
  fflush (stdout);
}

void user_receive_array (software__array_type data);
void user_receive_array (software__array_type data)
{
  int i;
  printf("Receive array: ");
  for (i = 0; i < 16; i++)
    {assert (data[i] == i);}

  printf ("OK \n");
  fflush(stdout);
}


/* Appel des fonctions */
EMIT_TYPE_INT(integer, int32_t, "%d")
RECEIVE_TYPE_INT(integer, int32_t, "%d")

EMIT_TYPE_INT(natural, int64_t, "%lld")
RECEIVE_TYPE_INT(natural, int64_t, "%lld")

EMIT_TYPE_INT(int8,int8_t, "%hhd")
RECEIVE_TYPE_INT(int8,int8_t, "%hhd")

EMIT_TYPE_INT(int16,int16_t, "%d")
RECEIVE_TYPE_INT(int16,int16_t, "%d")

EMIT_TYPE_INT(int32,int32_t, "%d")
RECEIVE_TYPE_INT(int32,int32_t, "%d")

EMIT_TYPE_INT(int64,int64_t, "%ld")
RECEIVE_TYPE_INT(int64,int64_t, "%ld")

EMIT_TYPE_INT(uint8,uint8_t, "%hhu")
RECEIVE_TYPE_INT(uint8,uint8_t, "%hhu")

EMIT_TYPE_INT(uint16,uint16_t, "%u")
RECEIVE_TYPE_INT(uint16,uint16_t, "%u")

EMIT_TYPE_INT(uint32,uint32_t,"%u")
RECEIVE_TYPE_INT(uint32,uint32_t, "%u")

EMIT_TYPE_INT(uint64,uint64_t, "%lu")
RECEIVE_TYPE_INT(uint64,uint64_t, "%lu")

EMIT_TYPE_FLOAT(float0,float_t, "%lf")
RECEIVE_TYPE_FLOAT(float0,float_t, "%lf")

EMIT_TYPE_FLOAT(float32,float_t, "%lf")
RECEIVE_TYPE_FLOAT(float32,float_t, "%lf")

EMIT_TYPE_FLOAT(float64,double_t, "%llf")
RECEIVE_TYPE_FLOAT(float64,double_t,"%llf")
