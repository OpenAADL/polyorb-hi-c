#define __PO_HI_MESSAGES_MAX_SIZE 1

/*@
  @ ensures \result == __PO_HI_MESSAGES_MAX_SIZE;
  @*/
int foo() {
    return __PO_HI_MESSAGES_MAX_SIZE;
}
