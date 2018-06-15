#include <stdio.h>
#include <stdint.h>
#include <math.h>
#include <stdbool.h>
#include <string.h>

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

float_t float0_type_var = 0;
float_t float32_type_var = 0;
double_t float64_type_var = 0;
char character_type_var = '@';

/* Macros Definition */

/* Integer */

#define EMIT_TYPE_INT(TYPE,FORMAT)		\
  void user_emit_##TYPE (FORMAT##* type)	\
  {\
    TYPE##_type_var++;				\
      *type = TYPE##_type_var;\
      printf("Emetting integer : %d\n", *type);\
	}\
  }

#define RECEIVE_TYPE_INT(TYPE,FORMAT)			\
  void user_receive_##TYPE (FORMAT type)\
  {\
    printf("Receiving integer : %d\n" ,type);\
  }

/* Float */

#define EMIT_TYPE_FLOAT(TYPE, FORMAT)		\
  void user_emit_##TYPE (FORMAT##* type)	\
  {\
    TYPE##_type_var++;				\
      *type = TYPE##_type_var;\
      printf("Emetting float : %lf\n", *type);\
	}\
  }

#define RECEIVE_TYPE_FLOAT(TYPE,FORMAT)		\
  void user_receive_##TYPE (FORMAT type)\
  {\
    printf("Receiving float : %lf\n" ,type);\
  }


/* Boolean sub case */
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
}

void user_receive_boolean (int16_t boolean)
{
  printf ("Receiving boolean : %d\n", boolean);
}


/* Char sub case */

void user_emit_char (char* character)
{

  char_type_var =  'A' + ((char_type_var - 'A' +1) %26) ;
  *character = (char)char_type_var;

  printf ("Emetting char : %c\n", *character);
}

void user_receive_char (char character)
{
  printf ("Receiving char : %c\n", character);
}

/* Appel des fonctions */
EMIT_TYPE_INT(integer,int32_t)
RECEIVE_TYPE_INT(integer,int32_t)

EMIT_TYPE_INT(natural,int64_t)
RECEIVE_TYPE_INT(natural,int64_t)

EMIT_TYPE_INT(int8,int8_t)
RECEIVE_TYPE_INT(int8,int8_t)

EMIT_TYPE_INT(int16,int16_t)
RECEIVE_TYPE_INT(int16,int16_t)

EMIT_TYPE_INT(int32,int32_t)
RECEIVE_TYPE_INT(int32,int32_t)

EMIT_TYPE_INT(int64,int64_t)
RECEIVE_TYPE_INT(int64,int64_t)

EMIT_TYPE_INT(uint8,uint8_t)
RECEIVE_TYPE_INT(uint8,uint8_t)

EMIT_TYPE_INT(uint16,uint16_t)
RECEIVE_TYPE_INT(uint16,uint16_t)

EMIT_TYPE_INT(uint32,uint32_t)
RECEIVE_TYPE_INT(uint32,uint32_t)

EMIT_TYPE_INT(uint64,uint64_t)
RECEIVE_TYPE_INT(uint64,uint64_t)

EMIT_TYPE_FLOAT(float0,float_t)
RECEIVE_TYPE_FLOAT(float0,float_t)

EMIT_TYPE_FLOAT(float32,float_t)
RECEIVE_TYPE_FLOAT(float32,float_t)

EMIT_TYPE_FLOAT(float64,double_t)
RECEIVE_TYPE_FLOAT(float64,double_t)
