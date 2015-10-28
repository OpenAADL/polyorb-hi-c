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
#include <po_hi_utils.h>
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
