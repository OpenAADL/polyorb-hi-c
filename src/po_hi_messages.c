/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://assert-project.net/taste
 *
 * Copyright (C) 2007-2009 Telecom ParisTech, 2010-2012 ESA & ISAE.
 */

#include <po_hi_config.h>
#include <po_hi_types.h>
#include <po_hi_messages.h>

/* Headers from PolyORB-HI-C */

#if defined (__CYGWIN__) || defined (__MINGW32__)
#else
#include <xlocale.h>
#endif
#include <string.h>

/* Headers from the executive */

#ifdef __PO_HI_DEBUG
#include <stdio.h>
#endif

__po_hi_uint8_t* memset_uint8(__po_hi_uint8_t* s, int c, size_t n)
{
    return memset (s, c, n);
}

void __po_hi_msg_reallocate (__po_hi_msg_t* message)
{
         message->length = 0;
         message->flags = 0;
         memset_uint8 (message->content, 0, __PO_HI_MESSAGES_MAX_SIZE);
}

void __po_hi_msg_write (__po_hi_msg_t*  msg, __po_hi_uint8_t* data, __po_hi_uint32_t len)
{
         msg->length = len;
         __po_hi_copy_array_uint8  (msg->content, data, len);
}

void __po_hi_msg_read (__po_hi_msg_t*  msg, __po_hi_uint8_t* data, __po_hi_uint32_t len)
{
         __po_hi_copy_array_uint8 (data, msg->content, len);
         msg->length -= len;
}

__po_hi_uint32_t __po_hi_msg_length (__po_hi_msg_t* msg)
{
         return (msg->length);
}

void __po_hi_msg_copy (__po_hi_msg_t* dest, __po_hi_msg_t* src)
{
	dest->length = src->length;
	__po_hi_copy_array_uint8 (dest->content, src->content, __PO_HI_MESSAGES_MAX_SIZE);
}

void __po_hi_msg_append_data (__po_hi_msg_t* msg, __po_hi_uint8_t* data, __po_hi_uint32_t length)
{
	msg->length = msg->length + length;
	__po_hi_copy_array_uint8 (&(msg->content[msg->length - length]), data, length);
}

void __po_hi_msg_append_msg (__po_hi_msg_t* dest, __po_hi_msg_t* source)
{
	dest->length = dest->length + source->length;
	__po_hi_copy_array_uint8  (&(dest->content[dest->length - source->length]), source->content, source->length);
}

void __po_hi_msg_get_data (void* dest, __po_hi_msg_t* source, __po_hi_uint32_t index, __po_hi_uint32_t size)
{
	__po_hi_copy_array (dest, &(source->content[index]), size);
}

void __po_hi_msg_move (__po_hi_msg_t* msg, __po_hi_uint32_t length)
{
	 msg->length = msg->length - length;
	 __po_hi_uint32_t tmp;
   /*@ loop assigns tmp, msg->content[0..msg->length-1];
     @ loop invariant 0 <= tmp;
     @ loop invariant tmp <= \at(msg->length, Pre) - length;
     @ loop invariant \forall int i; 0 <= i < tmp ==> msg->content[i] == \at(msg->content[length + i], Pre);
     @ loop invariant \forall int i; tmp <= i < \at(msg->length, Pre) ==> msg->content[i] == \at(msg->content[i], Pre);
     @ loop variant msg->length - tmp;
    */
   for (tmp=0; tmp < msg->length ; tmp++)
   {
      msg->content[tmp] = msg->content[length + tmp];
   }
}

#ifdef __PO_HI_USE_GIOP
int __po_hi_msg_should_swap (__po_hi_msg_t* msg)
{
#ifdef WORDS_BIGENDIAN
        if (msg->flags == __PO_HI_MESSAGES_CONTENT_LITTLEENDIAN)
        {
                return 1;
        }
#else
        if (msg->flags == __PO_HI_MESSAGES_CONTENT_BIGENDIAN)
        {
                return 1;
        }
#endif
        return 0;
}

void __po_hi_msg_swap_value (void* from, void* dest, __po_hi_uint8_t size)
{
        __po_hi_uint8_t tmp;
        __po_hi_uint8_t* udest;
        __po_hi_uint8_t* ufrom;

        ufrom = (__po_hi_uint8_t*)from;
        udest = (__po_hi_uint8_t*)dest;

        for (tmp=0 ; tmp < size ; tmp++)
        {
                udest[tmp] = ufrom[size-tmp];
        }
}
#endif

#ifdef __PO_HI_DEBUG
void __po_hi_messages_debug (__po_hi_msg_t* msg)
{
   uint32_t length;
   char Hexa [50];
   char ASCII [17];
   int Index_Hexa = 0;
   int Index_ASCII = 0;
   int i;

   for (i = 0 ; i < 50 ; i++)
     Hexa[i] = ' ';

   for (i = 0 ; i < 17 ; i++)
     ASCII[i] = ' ';

   printf ("Length: %u\n", (unsigned int) msg->length);

   for (length = 0 ; length < msg->length ; length++)
   {
     Hexa [Index_Hexa] = ' ';

     if ((msg->content[length]/16) > 9)
       Hexa [Index_Hexa + 1] = 'A' -10 + (msg->content[length] / 16);
     else
       Hexa [Index_Hexa + 1] = '0' + (msg->content[length] / 16);

     if ((msg->content[length] % 16) > 9)
       Hexa [Index_Hexa + 2] = 'A' - 10 + (msg->content[length] % 16);
     else
       Hexa [Index_Hexa + 2] = '0' + (msg->content[length] % 16);

     Index_Hexa += 3;

     if ((msg->content[length] < 32) || (msg->content[length] > 127))
       ASCII [Index_ASCII] = '.';
     else
       ASCII [Index_ASCII] = msg->content[length];

     Index_ASCII++;

     if (Index_Hexa >= 45)
       {
	 Hexa[Index_Hexa] = '\0';
	 ASCII[Index_ASCII] = '\0';
	 printf ("%s  ||  %s\n", Hexa, ASCII);
	 Index_Hexa = 0;
	 Index_ASCII = 0;
	 for (i = 0 ; i < 50 ; i++)
	   Hexa[i] = ' ';

	 for (i = 0 ; i < 17 ; i++)
	   ASCII[i] = ' ';
       }
   }
   if (Index_Hexa > 0)
     {
       for (i = Index_Hexa ; i<44 ; i++)
	 Hexa[i] = ' ';
       Index_Hexa = 45;

       Hexa[Index_Hexa] = '\0';
       ASCII[Index_ASCII] = '\0';
       printf ("%s  ||  %s\n", Hexa, ASCII);
     }

}
#endif
