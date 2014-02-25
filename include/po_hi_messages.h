/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://assert-project.net/taste
 *
 * Copyright (C) 2007-2009 Telecom ParisTech, 2010-2012 ESA & ISAE.
 */

#ifndef __PO_HI_MESSAGES_H_
#define __PO_HI_MESSAGES_H_

#include <po_hi_config.h>
#include <po_hi_types.h>
#include <stddef.h>

#include <request.h>
/* This file may not be generated. However, using messages implies
   using request. */

#ifdef __PO_HI_USE_GIOP
#define __PO_HI_MESSAGES_MAX_SIZE (int) sizeof(__po_hi_request_t) + 200
#else
#define __PO_HI_MESSAGES_MAX_SIZE (int) sizeof(__po_hi_request_t) + 4
/* XXX Why + 4 ? to be investigated */
#endif

#define __PO_HI_MESSAGES_CONTENT_BIGENDIAN      1
#define __PO_HI_MESSAGES_CONTENT_LITTLEENDIAN   2

typedef struct
{
  __po_hi_uint32_t  length;
  __po_hi_uint8_t   flags;
  __po_hi_uint8_t   content[__PO_HI_MESSAGES_MAX_SIZE]; /* Content of the message */
} __po_hi_msg_t;

/*
 * memset variant for uint8 arrays.
 */
/*@ requires \valid(s+(0..n-1));
  @ assigns s[0..n-1];
  @ ensures \forall int i; 0 <= i < n ==> *(s+i) == c;
  @ ensures \result == s;
  @*/
__po_hi_uint8_t* memset_uint8(__po_hi_uint8_t* s, int c, size_t n);

/*
 * Reset the message given in parameter
 */
/*@ requires \valid(message);
  @ requires \valid(message->content+(0..(__PO_HI_MESSAGES_MAX_SIZE - 1)));
  @ requires \separated(message->content+(0..(__PO_HI_MESSAGES_MAX_SIZE - 1)), &(message->flags));
  @ requires \separated(message->content+(0..(__PO_HI_MESSAGES_MAX_SIZE - 1)), &(message->length));
  @ assigns message->length;
  @ assigns message->flags;
  @ assigns message->content[0..(__PO_HI_MESSAGES_MAX_SIZE - 1)];
  @ ensures message->flags == 0;
  @ ensures message->length == 0;
  @ ensures \forall int i; 0 <= i < __PO_HI_MESSAGES_MAX_SIZE - 1 ==> message->content[i] == 0;
 */
void __po_hi_msg_reallocate (__po_hi_msg_t* message);

/*
 * Write the data at the beginning of the specified message.  Length
 * of the data are specified by the parameter len
 */
/*@ requires \valid(msg);
  @ requires \valid(msg->content+(0..len-1));
  @ requires \valid(data+(0..len-1));
  @ requires \separated(msg->content+(0..len-1), data+(0..len-1));
  @ assigns msg->content[0..len-1];
  @ assigns msg->length;
  @ ensures msg->length == len;
  @ ensures \forall int i; 0 <= i < len ==> msg->content[i] == data[i];
  @*/
void __po_hi_msg_write (__po_hi_msg_t*  msg, __po_hi_uint8_t* data, __po_hi_uint32_t len);

/*
 * Read the data in the specified message. The data are taken from the
 * message and copied into the variable data.  Length of the data are
 * specified by the parameter len
 */
/*@ requires \valid(msg);
  @ requires \valid(msg->content+(0..len-1));
  @ requires \valid(data+(0..len-1));
  @ requires len <= msg->length;
  @ requires \separated(msg->content+(0..len-1), data+(0..len-1));
  @ requires \separated(&(msg->length), data+(0..len-1));
  @ assigns data[0..len-1];
  @ assigns msg->length;
  @ ensures msg->length == \old(msg->length) - len;
  @ ensures \forall int i; 0 <= i < len ==> data[i] == msg->content[i];
  @*/
void __po_hi_msg_read (__po_hi_msg_t*  msg, __po_hi_uint8_t* data, __po_hi_uint32_t len);

/*
 * Return the length is the message
 */
/*@ requires \valid(msg);
  @ assigns \nothing;
  @ ensures \result == msg->length;
 */
__po_hi_uint32_t __po_hi_msg_length (__po_hi_msg_t* msg);

/*
 * Copy a message. The first argument is the message destination
 * whereas the second argument is the message source
 */
/*@ requires \valid(dest);
  @ requires \valid(src);
  @ requires \valid(dest->content+(0..(__PO_HI_MESSAGES_MAX_SIZE - 1)));
  @ requires \valid(src->content+(0..(__PO_HI_MESSAGES_MAX_SIZE - 1)));
  @ requires \separated(dest->content+(0..(__PO_HI_MESSAGES_MAX_SIZE - 1)), src->content+(0..(__PO_HI_MESSAGES_MAX_SIZE - 1)));
  @ assigns dest->length;
  @ assigns dest->content[0..(__PO_HI_MESSAGES_MAX_SIZE - 1)];
  @ ensures dest->length == \old(src->length);
  @ ensures \forall int i; 0 <= i < __PO_HI_MESSAGES_MAX_SIZE ==> src->content[i] == dest->content[i];
 */
void __po_hi_msg_copy (__po_hi_msg_t* dest,
		       __po_hi_msg_t* src);

/*
 * Append data to a message. The first argument is the message which
 * will contain all the data. The second argument is a pointer to the
 * data and the third argument (length) is the size of the data in
 * byte.
 */
/*@ requires \valid(msg);
  @ requires \valid(msg->content+(0..(msg->length + length - 1)));
  @ requires \valid(data+(0..(length - 1)));
  @ requires \separated(msg->content+(msg->length..msg->length + length - 1), data+(0..(length - 1)));
  @ requires msg->length + length <= __PO_HI_MESSAGES_MAX_SIZE;
  @ assigns msg->content[msg->length..(msg->length + length - 1)];
  @ assigns msg->length;
  @ ensures \forall int i; 0 <= i < length ==> msg->content[\old(msg->length) + i] == data[i];
  @ ensures msg->length == \old(msg->length) + length;
  @*/
void __po_hi_msg_append_data (__po_hi_msg_t* msg, __po_hi_uint8_t* data, __po_hi_uint32_t length);

/*
 * Append a message to another message. The first argument is the
 * message in which we will append the data. The second argument is
 * the source of the data.
 */
/*@ requires \valid(dest);
  @ requires \valid(source);
  @ requires \valid(dest->content+(0..(dest->length + source->length - 1)));
  @ requires \valid(source->content+(0..(source->length - 1)));
  @ requires source->length + dest->length <= __PO_HI_MESSAGES_MAX_SIZE;
  @ requires \separated(source->content+(0..source->length - 1), dest->content+(0..(dest->length + source->length - 1)));
  @ requires \separated(source->content+(0..source->length - 1), &(dest->length));
  @ requires \separated(dest->content+(0..(dest->length + source->length - 1)), &(source->length));
  @ requires &(source->length) != &(dest->length);
  @ assigns dest->content[dest->length..(dest->length + source->length - 1)];
  @ assigns dest->length;
  @ ensures \forall int i; 0 <= i < source->length ==> dest->content[\old(dest->length) + i] == source->content[i];
  @ ensures dest->length == \old(dest->length) + source->length;
  @ ensures source->length == \old(source->length);
  @*/
void __po_hi_msg_append_msg (__po_hi_msg_t* dest, __po_hi_msg_t* source);

/*
 * Get data from a message at index 'index', and copy it to the dest
 * argument It will copy size bytes from the messages.
 */
/*@ requires \valid(source);
  @ requires \valid(dest+(0..size-1));
  @ requires \valid(source->content+(index..(index+size-1)));
  @ requires index >= 0;
  @ requires index + size <= source->length;
  @ requires \separated(dest+(0..size-1),(source->content)+(index..(index+size-1)));
  @ assigns dest[0..(size - 1)];
  @ ensures \forall int i; 0 <= i < size ==> dest[i] == (source->content + index)[i];
  @*/
void __po_hi_msg_get_data (__po_hi_uint8_t* dest, __po_hi_msg_t* source,
                           __po_hi_uint32_t index,
                           __po_hi_uint32_t size);

/*@ requires \valid(msg);
  @ requires \valid(msg->content+(0..msg->length-1));
  @ requires length > 0;
  @ requires length <= msg->length;
  @ requires msg->length <= __PO_HI_MESSAGES_MAX_SIZE;
  @ requires \separated(msg->content+(0..msg->length-1), &(msg->length));
  @ assigns msg->content[0..msg->length - length - 1];// \from msg->content[length..msg->length - 1];
  @ assigns msg->length;
  @ ensures \forall int i; 0 <= i < msg->length ==> msg->content[i] == \old(msg->content[length + i]);
  @ ensures msg->length == \old(msg->length) - length;
 */
void __po_hi_msg_move (__po_hi_msg_t* msg, __po_hi_uint32_t length);
/*
 * Move a part of the message to the beginning. This function will put
 * the part (starting from the length argument) to the beginning of
 * the message.
 */

#ifdef __PO_HI_USE_GIOP
int __po_hi_msg_should_swap (__po_hi_msg_t* msg);
/*
 * The __po_hi_msg_should_swap return 1 if the endianness of the
 * current processor differs with the endianness of the message. Else,
 * it returns 0.
 */

void __po_hi_msg_swap_value (void* from, void* dest, __po_hi_uint8_t size);
/*
 * The function __po_hi_msg_swap_value swap the bytes of the from
 * value and put it to the dest argument. The size of the value is
 * designed by the third argument.
 */
#endif /* __PO_HI_USE_GIOP */

#ifdef __PO_HI_DEBUG
void __po_hi_messages_debug (__po_hi_msg_t* msg);
#endif

#endif /* __PO_HI_MESSAGES_H_ */
