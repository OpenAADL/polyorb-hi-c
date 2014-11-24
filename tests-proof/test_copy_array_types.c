#include "po_hi_types.h"

/*@ requires \valid(dst+(0..4));
  @ requires \valid(src+(0..4));
  @ requires \separated(dst+(0..4), src+(0..4));
  @ ensures \forall int i; 0 <= i < 4 ==> *(dst+i) == *(src+i);
  @*/
void test_five_int_to_be_copied_behavior (__po_hi_uint8_t* dst, __po_hi_uint8_t* src) {
    __po_hi_copy_array_uint8(dst, src, 4);
}
