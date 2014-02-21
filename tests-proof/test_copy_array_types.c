#include "po_hi_types.h"

/*@ requires \valid(dst+(0..4));
  @ requires \valid(src+(0..4));
  @ requires \separated(dst+(0..4), src+(0..4));
  @ ensures \forall int i; 0 <= i < 5 ==> *(dst+i) == *(src+i);
  @*/
void test_five_int_to_be_copied_behavior (int* dst, int* src) {
    __po_hi_copy_array(dst, src, 20);
}
