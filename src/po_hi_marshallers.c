/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2009, GET-Telecom Paris.
 */

#include <po_hi_config.h>
#include <po_hi_marshallers.h>
#include <po_hi_messages.h>
/* headers from PolyORB-HI-C */

#include <request.h>
#include <deployment.h>
/* headers from the generated code */

#ifdef __PO_HI_USE_GIOP
#include <string.h>
#endif
/* should be made with our own allocator, such as
   a big array that we handle by hand
*/

/*
 * This file provides some useful function to marshall and unmarshall data.
 * It handles several protocols.
 *
 * For the GIOP protocol, we perform an alignment of the data. Currently,
 * the data are aligned like this :
 * - int                  is aligned to 4 bytes
 * - __po_hi_int16_t      is aligned to 4 bytes
 * - __po_hi_int32_t      is aligned to 4 bytes
 * - __po_hi_int8_t       is aligned to 1 byte (we consider this type as a character)
 */


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
void __po_hi_marshall_port (__po_hi_port_t value, __po_hi_msg_t* msg)
{
        __po_hi_msg_append_data (msg, &value, sizeof(__po_hi_port_t));
}

void __po_hi_unmarshall_port (__po_hi_port_t* value, __po_hi_msg_t* msg)
{
        /*
         * The operation is always written by the local machine, or
         * received with the raw protocol. So, we don't have to check
         * byte order for it
         */
        __po_hi_msg_get_data (value, msg, 0, sizeof (__po_hi_port_t));
}

/*
 * Array marshallers
 */
void __po_hi_marshall_array (void* value, __po_hi_msg_t* msg,__po_hi_uint32_t size, __po_hi_uint32_t* offset)
{
#ifdef __PO_HI_USE_GIOP
        __po_hi_find_alignment (4, msg, offset);
#endif
        __po_hi_msg_append_data (msg, value, size);
        *offset = *offset + size; 
}

void __po_hi_unmarshall_array (void* value, __po_hi_msg_t* msg,__po_hi_uint32_t size, __po_hi_uint32_t* offset)
{
#ifdef __PO_HI_USE_GIOP
        __po_hi_uint8_t tmpvalue[size];

        __po_hi_find_alignment (4, msg, offset);
#endif

        __po_hi_msg_get_data (value, msg, *offset + sizeof (__po_hi_port_t), size);

#ifdef __PO_HI_USE_GIOP
        if (__po_hi_msg_should_swap (msg))
        {
           __po_hi_msg_swap_value (value, tmpvalue, size);
           memcpy (value, tmpvalue, size);
        }
#endif

        *offset = *offset + size; 
}

/*
 * __po_hi_bool_t marshallers
 */

void __po_hi_marshall_bool (__po_hi_bool_t value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
  __po_hi_msg_append_data (msg, &value, sizeof(__po_hi_bool_t));
  *offset = *offset + sizeof (__po_hi_bool_t); 
}

void __po_hi_unmarshall_bool (__po_hi_bool_t* value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
  __po_hi_msg_get_data (value, msg, *offset + sizeof (__po_hi_port_t), sizeof(__po_hi_bool_t));
  *offset = *offset + sizeof (__po_hi_bool_t); 
}

/*
 * char marshallers
 */

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


/*
 * Integer marshallers
 */
void __po_hi_marshall_int (int value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
#ifdef __PO_HI_USE_GIOP
        __po_hi_find_alignment (4, msg, offset);
#endif
        __po_hi_msg_append_data (msg, &value, sizeof(int));
        *offset = *offset + sizeof (int); 
}

void __po_hi_unmarshall_int (int* value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
#ifdef __PO_HI_USE_GIOP
        int tmpvalue;

        __po_hi_find_alignment (4, msg, offset);
#endif

        __po_hi_msg_get_data (value, msg, *offset + sizeof (__po_hi_port_t), sizeof(int));

#ifdef __PO_HI_USE_GIOP
        if (__po_hi_msg_should_swap (msg))
        {
                __po_hi_msg_swap_value (value, &tmpvalue, sizeof (int));
                *value = tmpvalue;
        }
#endif

        *offset = *offset + sizeof (int); 
}

/*
 * Float Marshallers
 */

void __po_hi_marshall_float (float value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
#ifdef __PO_HI_USE_GIOP
        __po_hi_find_alignment (4, msg, offset);
#endif

        __po_hi_msg_append_data (msg, &value, sizeof(float));
        *offset = *offset + sizeof (float); 
}

void __po_hi_unmarshall_float (float* value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
#ifdef __PO_HI_USE_GIOP
        float tmpvalue;
        __po_hi_find_alignment (4, msg, offset);
#endif

        __po_hi_msg_get_data (value, msg, *offset + sizeof (__po_hi_port_t), sizeof(float));

#ifdef __PO_HI_USE_GIOP
        if (__po_hi_msg_should_swap (msg))
        {
                __po_hi_msg_swap_value (value, &tmpvalue, sizeof (float));
                *value = tmpvalue;
        }
#endif
        *offset = *offset + sizeof (float); 
}


void __po_hi_marshall_float32 (__po_hi_float32_t value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
#ifdef __PO_HI_USE_GIOP
        __po_hi_find_alignment (4, msg, offset);
#endif

        __po_hi_msg_append_data (msg, &value, sizeof(__po_hi_float32_t));
        *offset = *offset + sizeof (__po_hi_float32_t); 
}

void __po_hi_unmarshall_float32 (__po_hi_float32_t* value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
#ifdef __PO_HI_USE_GIOP
        float tmpvalue;
        __po_hi_find_alignment (4, msg, offset);
#endif

        __po_hi_msg_get_data (value, msg, *offset + sizeof (__po_hi_port_t), sizeof(__po_hi_float32_t));

#ifdef __PO_HI_USE_GIOP
        if (__po_hi_msg_should_swap (msg))
        {
                __po_hi_msg_swap_value (value, &tmpvalue, sizeof (__po_hi_float32_t));
                *value = tmpvalue;
        }
#endif
        *offset = *offset + sizeof (__po_hi_float32_t); 
}

void __po_hi_marshall_float64 (__po_hi_float64_t value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
        __po_hi_msg_append_data (msg, &value, sizeof(__po_hi_float64_t));
        *offset = *offset + sizeof (__po_hi_float64_t); 
}

void __po_hi_unmarshall_float64 (__po_hi_float64_t* value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
        __po_hi_msg_get_data (value, msg, *offset + sizeof (__po_hi_port_t), sizeof(__po_hi_float64_t));
        *offset = *offset + sizeof (__po_hi_float64_t); 
}

/*
 * __po_hi_int8_t marshallers
 */

void __po_hi_marshall_int8 (__po_hi_int8_t value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
        __po_hi_msg_append_data (msg, &value, sizeof(__po_hi_int8_t));
        *offset = *offset + sizeof (__po_hi_int8_t); 
}

void __po_hi_unmarshall_int8 (__po_hi_int8_t* value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
        __po_hi_msg_get_data (value, msg, *offset + sizeof (__po_hi_port_t), sizeof(__po_hi_int8_t));
        *offset = *offset + sizeof (__po_hi_int8_t); 
}

/*
 * __po_hi_int16_t marshallers
 */

void __po_hi_marshall_int16 (__po_hi_int16_t value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
#ifdef __PO_HI_USE_GIOP
        __po_hi_find_alignment (4, msg, offset);
#endif
        __po_hi_msg_append_data (msg, &value, sizeof(__po_hi_int16_t));
        *offset = *offset + sizeof (__po_hi_int16_t); 
}

void __po_hi_unmarshall_int16 (__po_hi_int16_t* value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
#ifdef __PO_HI_USE_GIOP
        __po_hi_int16_t tmpvalue;
        __po_hi_find_alignment (4, msg, offset);
#endif

        __po_hi_msg_get_data (value, msg, *offset + sizeof (__po_hi_port_t), sizeof(__po_hi_int16_t));

#ifdef __PO_HI_USE_GIOP
        if (__po_hi_msg_should_swap (msg))
        {
                __po_hi_msg_swap_value (value, &tmpvalue, sizeof (__po_hi_int16_t));
                *value = tmpvalue;
        }
#endif
        *offset = *offset + sizeof (__po_hi_int16_t); 
}

/*
 * __po_hi_int32_t marshallers
 */

void __po_hi_marshall_int32 (__po_hi_int32_t value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
#ifdef __PO_HI_USE_GIOP
        __po_hi_find_alignment (4, msg, offset);
#endif
        __po_hi_msg_append_data (msg, &value, sizeof(__po_hi_int32_t));
        *offset = *offset + sizeof (__po_hi_int32_t); 
}

void __po_hi_unmarshall_int32 (__po_hi_int32_t* value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
#ifdef __PO_HI_USE_GIOP
        __po_hi_int32_t tmpvalue;
        __po_hi_find_alignment (4, msg, offset);
#endif
        __po_hi_msg_get_data (value, msg, *offset + sizeof (__po_hi_port_t), sizeof(__po_hi_int32_t));

#ifdef __PO_HI_USE_GIOP
        if (__po_hi_msg_should_swap (msg))
        {
                __po_hi_msg_swap_value (value, &tmpvalue, sizeof (__po_hi_int32_t));
                *value = tmpvalue;
        }
#endif
        *offset = *offset + sizeof (__po_hi_int32_t); 
}

/*
 * __po_hi_int64_t marshallers
 */

void __po_hi_marshall_int64 (__po_hi_int64_t value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
        __po_hi_msg_append_data (msg, &value, sizeof(__po_hi_int64_t));
        *offset = *offset + sizeof (__po_hi_int64_t); 
}

void __po_hi_unmarshall_int64 (__po_hi_int64_t* value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
        __po_hi_msg_get_data (value, msg, *offset + sizeof (__po_hi_port_t), sizeof(__po_hi_int64_t));
        *offset = *offset + sizeof (__po_hi_int64_t); 
}


/*
 * __po_hi_uint8_t marshallers
 */

void __po_hi_marshall_uint8 (__po_hi_uint8_t value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
        __po_hi_msg_append_data (msg, &value, sizeof(__po_hi_uint8_t));
        *offset = *offset + sizeof (__po_hi_uint8_t); 
}

void __po_hi_unmarshall_uint8 (__po_hi_uint8_t* value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
        __po_hi_msg_get_data (value, msg, *offset + sizeof (__po_hi_port_t), sizeof(__po_hi_uint8_t));
        *offset = *offset + sizeof (__po_hi_uint8_t); 
}

/*
 * __po_hi_uint16_t marshallers
 */

void __po_hi_marshall_uint16 (__po_hi_uint16_t value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
#ifdef __PO_HI_USE_GIOP
        __po_hi_find_alignment (4, msg, offset);
#endif
        __po_hi_msg_append_data (msg, &value, sizeof(__po_hi_uint16_t));
        *offset = *offset + sizeof (__po_hi_uint16_t); 
}

void __po_hi_unmarshall_uint16 (__po_hi_uint16_t* value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
#ifdef __PO_HI_USE_GIOP
        __po_hi_uint16_t tmpvalue;
        __po_hi_find_alignment (4, msg, offset);
#endif

        __po_hi_msg_get_data (value, msg, *offset + sizeof (__po_hi_port_t), sizeof(__po_hi_uint16_t));

#ifdef __PO_HI_USE_GIOP
        if (__po_hi_msg_should_swap (msg))
        {
                __po_hi_msg_swap_value (value, &tmpvalue, sizeof (__po_hi_uint16_t));
                *value = tmpvalue;
        }
#endif
        *offset = *offset + sizeof (__po_hi_uint16_t); 
}

/*
 * __po_hi_uint32_t marshallers
 */

void __po_hi_marshall_uint32 (__po_hi_uint32_t value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
#ifdef __PO_HI_USE_GIOP
        __po_hi_find_alignment (4, msg, offset);
#endif
        __po_hi_msg_append_data (msg, &value, sizeof(__po_hi_uint32_t));
        *offset = *offset + sizeof (__po_hi_uint32_t); 
}

void __po_hi_unmarshall_uint32 (__po_hi_uint32_t* value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
#ifdef __PO_HI_USE_GIOP
        __po_hi_uint32_t tmpvalue;
        __po_hi_find_alignment (4, msg, offset);
#endif
        __po_hi_msg_get_data (value, msg, *offset + sizeof (__po_hi_port_t), sizeof(__po_hi_uint32_t));

#ifdef __PO_HI_USE_GIOP
        if (__po_hi_msg_should_swap (msg))
        {
                __po_hi_msg_swap_value (value, &tmpvalue, sizeof (__po_hi_uint32_t));
                *value = tmpvalue;
        }
#endif
        *offset = *offset + sizeof (__po_hi_uint32_t); 
}

/*
 * __po_hi_uint64_t marshallers
 */

void __po_hi_marshall_uint64 (__po_hi_uint64_t value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
        __po_hi_msg_append_data (msg, &value, sizeof(__po_hi_uint64_t));
        *offset = *offset + sizeof (__po_hi_uint64_t); 
}

void __po_hi_unmarshall_uint64 (__po_hi_uint64_t* value, __po_hi_msg_t* msg,__po_hi_uint32_t* offset)
{
        __po_hi_msg_get_data (value, msg, *offset + sizeof (__po_hi_port_t), sizeof(__po_hi_uint64_t));
        *offset = *offset + sizeof (__po_hi_uint64_t); 
}
