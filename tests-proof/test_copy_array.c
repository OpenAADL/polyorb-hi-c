#include "po_hi_types.h"

/*@ requires \valid(dst+(0..9));
  @ ensures \forall int i; 0 <= i < 10 ==> *(dst+i) == \old(*(dst+i));
  @*/
void test_nothing_to_be_copied_behavior (char* dst, char* src) {
    __po_hi_copy_array(dst, src, 0);
}

/*@ requires \valid(dst+(0..9));
  @ requires \valid(src+(0..9));
  @ requires \separated(dst+(0..9), src+(0..9));
  @ ensures \forall int i; 0 <= i < 5 ==> *(dst+i) == *(src+i);
  @ ensures \forall int i; 6 <= i < 10 ==> *(dst+i) == \old(*(dst+i));
  @*/
void test_five_to_be_copied_behavior (char* dst, char* src) {
    __po_hi_copy_array(dst, src, 5);
}

/*@ requires \valid(dst+(0..9));
  @ requires \valid(src+(0..9));
  @ requires \separated(dst+(0..9), src+(0..9));
  @ ensures \forall int i; 0 <= i < 10 ==> *(dst+i) == *(src+i);
  @*/
void test_ten_to_be_copied_behavior (char* dst, char* src) {
    __po_hi_copy_array(dst, src, 10);
}
