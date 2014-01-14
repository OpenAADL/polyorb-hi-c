#include "po_hi_messages.h"

/*@ requires \valid(dest->content+(0..dest->length-1));
  @ ensures \forall int i; 0 <= i < \old(dest->length) ==> *(dest->content+i) == \old(*(dest->content+i));
  @ ensures dest->length == \old(dest->length);
  @*/
void test_nothing_copied_msg_append_data(__po_hi_msg_t* dest, __po_hi_uint8_t* source) {
	__po_hi_msg_append_data (dest, source, 0);
}

/*@ requires \valid(dest->content+(0..dest->length+5-1)) && \valid(source+(0..4));
  @ requires \separated(dest->content+(0..dest->length+5-1), source+(0..4));
  @ requires \separated(&(dest->length), source+(0..4));
  @ ensures \forall int i; 0 <= i < \old(dest->length) ==> *(dest->content+i) == \old(*(dest->content+i));
  @ ensures \forall int i; 0 <= i < 5 ==> *(dest->content+\old(dest->length)+i) == *(source+i);
  @ ensures dest->length == \old(dest->length) + 5;
  @*/
void test_5_copied_msg_append_data(__po_hi_msg_t* dest, __po_hi_uint8_t* source) {
	__po_hi_msg_append_data (dest, source, 5);
}
