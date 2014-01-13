#include "po_hi_messages.h"

/*@ requires \valid(dest+(0..9));
  @ ensures \forall int i; 0 <= i < 10 ==> *(dest+i) == \old(*(dest+i));
  @*/
void test_nothing_copied_msg_get_data(__po_hi_uint8_t* dest, __po_hi_msg_t* source) {
	__po_hi_msg_get_data (dest, source, 0, 0);
}

/*@ requires \valid(dest+(0..9)) && \valid_read(source->content+(0..9));
  @ requires \separated(dest+(0..9), source->content+(0..9));
  @ ensures \forall int i; 0 <= i < 5 ==> *(dest+i) == *(source->content+i);
  @ ensures \forall int i; 5 <= i < 10 ==> *(dest+i) == \old(*(dest+i));
  @*/
void test_5_copied_msg_get_data(__po_hi_uint8_t* dest, __po_hi_msg_t* source) {
	__po_hi_msg_get_data (dest, source, 0, 5);
}

/*@ requires \valid(dest+(0..9)) && \valid_read(source->content+(5..9));
  @ requires \separated(dest+(0..9), source->content+(0..9));
  @ ensures \forall int i; 0 <= i < 5 ==> *(dest+i) == *(source->content+5+i);
  @ ensures \forall int i; 5 <= i < 10 ==> *(dest+i) == \old(*(dest+i));
  @*/
void test_5middle_copied_msg_get_data(__po_hi_uint8_t* dest, __po_hi_msg_t* source) {
	__po_hi_msg_get_data (dest, source, 5, 5);
}
