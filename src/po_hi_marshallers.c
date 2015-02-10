/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2007-2009 Telecom ParisTech, 2010-2014 ESA & ISAE.
 */

#include <po_hi_config.h>
#include <po_hi_marshallers.h>
#include <po_hi_messages.h>
#include <po_hi_transport.h>
/* headers from PolyORB-HI-C */

#include <request.h>
#include <deployment.h>
/* headers from the generated code */


/* Generic marshaller/unmarshaller macros */

#define TYPE_MARSHALLER(THE_TYPE) \
void __po_hi_marshall_##THE_TYPE (__po_hi_##THE_TYPE##_t value, __po_hi_msg_t* msg, __po_hi_uint32_t* offset) \
{ \
  __po_hi_##THE_TYPE##_t tmpvalue = value; \
\
  if (sizeof (__po_hi_##THE_TYPE##_t) > 1 && __po_hi_get_endianness (__PO_HI_MY_NODE) == __PO_HI_BIGENDIAN) \
    { \
      __po_hi_msg_swap_value (&value, &tmpvalue, sizeof (__po_hi_##THE_TYPE##_t)); \
    } \
  __po_hi_msg_append_data (msg, &tmpvalue, sizeof(__po_hi_##THE_TYPE##_t)); \
  *offset = *offset + sizeof (__po_hi_##THE_TYPE##_t); \
}

#define TYPE_UNMARSHALLER(THE_TYPE)  \
void __po_hi_unmarshall_##THE_TYPE (__po_hi_##THE_TYPE##_t* value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset) \
  { \
  __po_hi_##THE_TYPE##_t tmpvalue; \
  __po_hi_msg_get_data (value, msg, *offset + sizeof (__po_hi_port_t), sizeof(__po_hi_##THE_TYPE##_t)); \
\
  if (sizeof (__po_hi_##THE_TYPE##_t) > 1 && __po_hi_get_endianness (__PO_HI_MY_NODE) == __PO_HI_BIGENDIAN) \
    { \
      __po_hi_msg_swap_value (value, &tmpvalue, sizeof (__po_hi_##THE_TYPE##_t)); \
      *value = tmpvalue; \
    } \
 *offset = *offset + sizeof (__po_hi_##THE_TYPE##_t); \
 }

/* __po_hi_port_t marshallers */
// XXX why no update on offset ?

#ifdef __PO_HI_USE_GIOP
void __po_hi_find_alignment (__po_hi_uint8_t align, __po_hi_msg_t* msg, __po_hi_uint32_t* offset)
{
  __po_hi_uint16_t the_offset = *offset;
  while( (the_offset % align) != 0 )
    {
      the_offset++;
      msg->length++;
    }
}
#endif
/*
 * The function __po_hi_find_alignment was made to align data for GIOP
 * messages.  The first parameter is used to give to alignment value
 * in byte. The function search a correct value according to the
 * offset argument (current offset in the marshalled data). The size
 * of the message given in argument is increased to respect the
 * alignment.
 *
 * This function is defined for the GIOP protocol and is used only if
 * this protocol is chosen.
 */


/*
 * Operations Marshallers
 */

/* @	requires \valid(msg);
	requires \valid(msg->content+(0..(msg->length + sizeof(__po_hi_port_t))));

 	assigns (msg->content+(msg->length..msg->length + sizeof(__po_hi_port_t) - 1));

 	ensures msg->length == \old(msg->length) + sizeof(__po_hi_port_t);
 	ensures ((__po_hi_port_t *) msg->content)[\old(msg->length)] == value;
 */

/*@ requires \valid(msg);
  @ requires \valid(msg->content+(msg->length..(msg->length + sizeof(__po_hi_port_t) - 1)));
  @	requires \valid(((__po_hi_uint8_t*)value)+(0..(sizeof(__po_hi_port_t) - 1)));
  @	requires \separated(msg->content+(msg->length..msg->length + sizeof(__po_hi_port_t) - 1), ((__po_hi_uint8_t*)value)+(0..(sizeof(__po_hi_port_t) - 1)));
  @ requires \separated(msg->content+(msg->length..msg->length + sizeof(__po_hi_port_t) - 1), &(msg->length));
  @ requires \separated(((__po_hi_uint8_t*)value)+(0..(sizeof(__po_hi_port_t) - 1)), &(msg->length));
  @ requires msg->length + sizeof(__po_hi_port_t) <= 4294967295;
  @	assigns msg->content[msg->length..(msg->length + sizeof(__po_hi_port_t) - 1)] \from ((unsigned char*)value)[0..(sizeof(__po_hi_port_t) - 1)];
  @	assigns msg->length;
  @ //ensures \forall int i; 0 <= i < \old(msg->length) ==> msg->content[i] == \old(msg->content[i]);
  @	ensures \forall int i; 0 <= i < sizeof(__po_hi_port_t) ==> msg->content[\old(msg->length) + i] == ((__po_hi_uint8_t*)value) [i];
  @ ensures msg->length == \old(msg->length) + sizeof(__po_hi_port_t);
  */
void __po_hi_marshall_port (__po_hi_port_t value, __po_hi_msg_t* msg)
{
  __po_hi_msg_append_data (msg, &value, sizeof(__po_hi_port_t));
}

void __po_hi_unmarshall_port (__po_hi_port_t* value, __po_hi_msg_t* msg)
{
  /* The operation is always written by the local machine, or received
   * with the raw protocol. So, we don't have to check byte order */

  __po_hi_msg_get_data (value, msg, 0, sizeof (__po_hi_port_t));
}

/* array marshallers */

void __po_hi_marshall_array (void* value, __po_hi_msg_t* msg,__po_hi_uint32_t size, __po_hi_uint32_t* offset)
{
  __po_hi_msg_append_data (msg, value, size);
  *offset = *offset + size;
}

void __po_hi_unmarshall_array (void* value, __po_hi_msg_t* msg,__po_hi_uint32_t size, __po_hi_uint32_t* offset)
{
  __po_hi_msg_get_data (value, msg, *offset + sizeof (__po_hi_port_t), size);
  *offset = *offset + size;
}

#ifndef COMPCERT
/* __po_hi_bool_t marshallers */

TYPE_MARSHALLER (bool)
TYPE_UNMARSHALLER (bool)

#endif

/* char marshallers */

void __po_hi_marshall_char (char value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
  __po_hi_msg_append_data (msg, &value, sizeof(char));
  *offset = *offset + sizeof (char);
}

void __po_hi_unmarshall_char (char* value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
  __po_hi_msg_get_data (value, msg, *offset + sizeof (__po_hi_port_t), sizeof(char));
  *offset = *offset + sizeof (char);
}

/* integer marshallers */

void __po_hi_marshall_int (int value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
  int tmpvalue = value;

  if (sizeof (int) > 1 && __po_hi_get_endianness (__PO_HI_MY_NODE) == __PO_HI_BIGENDIAN)
    {
      __po_hi_msg_swap_value (&value, &tmpvalue, sizeof (int));
    }

  __po_hi_msg_append_data (msg, &tmpvalue, sizeof(int));
  *offset = *offset + sizeof (int);
}

void __po_hi_unmarshall_int (int* value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
  int tmpvalue;

  __po_hi_msg_get_data (value, msg, *offset + sizeof (__po_hi_port_t), sizeof(int));

  if (sizeof (int) > 1 && __po_hi_get_endianness (__PO_HI_MY_NODE) == __PO_HI_BIGENDIAN)
    {
      __po_hi_msg_swap_value (value, &tmpvalue, sizeof (int));
      *value = tmpvalue;
    }
  *offset = *offset + sizeof (int);
}

/* float marshallers */

void __po_hi_marshall_float (float value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
  float tmpvalue = value;

  if (sizeof (int) > 1 && __po_hi_get_endianness (__PO_HI_MY_NODE) == __PO_HI_BIGENDIAN)
    {
      __po_hi_msg_swap_value (&value, &tmpvalue, sizeof (float));
    }
  __po_hi_msg_append_data (msg, &tmpvalue, sizeof(float));
  *offset = *offset + sizeof (float);
}

void __po_hi_unmarshall_float (float* value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
  float tmpvalue;

  __po_hi_msg_get_data (value, msg, *offset + sizeof (__po_hi_port_t), sizeof(float));

  if (sizeof (float) > 1 && __po_hi_get_endianness (__PO_HI_MY_NODE) == __PO_HI_BIGENDIAN)
    {
      __po_hi_msg_swap_value (value, &tmpvalue, sizeof (float));
      *value = tmpvalue;
    }
  *offset = *offset + sizeof (float);
}

/* __po_hi_float32_t marshallers */

TYPE_MARSHALLER (float32)
TYPE_UNMARSHALLER (float32)

/* __po_hi_float64_t marshallers */

TYPE_MARSHALLER (float64)
TYPE_UNMARSHALLER (float64)

/* __po_hi_int8_t marshallers */

TYPE_MARSHALLER (int8)
TYPE_UNMARSHALLER (int8)

/* __po_hi_int16_t marshallers */

TYPE_MARSHALLER (int16)
TYPE_UNMARSHALLER (int16)

/* __po_hi_int32_t marshallers */

TYPE_MARSHALLER (int32)
TYPE_UNMARSHALLER (int32)

#ifndef COMPCERT
/* __po_hi_int64_t marshallers */

TYPE_MARSHALLER (int64)
TYPE_UNMARSHALLER (int64)
#endif

/* __po_hi_uint8_t marshallers */

TYPE_MARSHALLER (uint8)
TYPE_UNMARSHALLER (uint8)

/* __po_hi_uint16_t marshallers */

TYPE_MARSHALLER (uint16)
TYPE_UNMARSHALLER (uint16)

/* __po_hi_uint32_t marshallers */

TYPE_MARSHALLER (uint32)
TYPE_UNMARSHALLER (uint32)

#ifndef COMPCERT
/* __po_hi_uint64_t marshallers */

TYPE_MARSHALLER (uint64)
TYPE_UNMARSHALLER (uint64)

#endif
