/*@
  @ ensures \result == value >> 24;
  @*/
unsigned long shift_right_24(unsigned long value) {
    return value >> 24;
}

/*@
  @ ensures \result == (unsigned long) (value << 24);
  @*/
unsigned long shift_left_24(unsigned long value) {
    unsigned long v = value << 24;
    return v;
}

/*@
  @ ensures \result == (value & 0x000000ff);
  @*/
unsigned long filter_ff(unsigned long value) {
    return value & 0x000000ff;
}

/*@
  @ ensures \result == (value & 0x000000ff) >> 24;
  @*/
unsigned long filter_shift_right(unsigned long value) {
    return (value & 0x000000ff) >> 24;
}

/*@
  @ ensures \result == (unsigned long) ((value & 0x000000ff) << 24);
  @*/
unsigned long filter_shift_left(unsigned long value) {
    return (value & 0x000000ff) << 24;
}

// the following function can be proved by Qed. using trivial
// simplification.
/*@
  @ ensures \result == (((value & 0x000000ff) >> 24) | ((value & 0x0000ff00) >> 8));
  @*/
unsigned long partial_swap(unsigned long value) {
    return ((value & 0x000000ff) >> 24) | ((value & 0x0000ff00) >> 8);
}

// the following function cannot be proved! You have to cast to the
// "specification" to the correct integer type...
/*@
  @ ensures \result == (((value & 0x000000ff) >> 24) | ((value & 0x0000ff00) << 8) | ((value & 0x0000ff00) >> 8));
  @*/
unsigned long partial_swap_unvalid(unsigned long value) {
    return ((value & 0x000000ff) >> 24) | ((value & 0x0000ff00) << 8) | ((value & 0x0000ff00) >> 8);
}


/*@
  @ ensures \result == ((value & 0x000000ff) << 24) +
  @                    ((value & 0x0000ff00) << 8)  +
  @                    ((value & 0x00ff0000) >> 8)  +
  @                    ((value & 0xff000000) >> 24);
  @*/
unsigned long swap_shift_unvalid(unsigned long value) {
    unsigned long v1 = (value & 0x000000ff) << 24;
    unsigned long v2 = (value & 0x0000ff00) << 8;
    unsigned long v3 = (value & 0x00ff0000) >> 8;
    unsigned long v4 = (value & 0xff000000) >> 24;

    unsigned long v = v1 + v2 + v3 + v4;

    return v;
}

// an implementation of swap bytes that can be proved. The
// intermediate assertions are not necessary.
/*@
  @ ensures \result == (((unsigned long) ((value & 0x000000ff) << 24)) |
  @                     ((unsigned long) ((value & 0x0000ff00) << 8))  |
  @                     ((value & 0x00ff0000) >> 8)                    |
  @                     ((value & 0xff000000) >> 24));
  @*/
unsigned long swap_shift(unsigned long value) {
    unsigned long v = 0;

    v |= ((value & 0x000000ff) << 24);
    //@ assert v == (unsigned long) ((value & 0x000000ff) << 24);
    //@ ghost left_shift_24:

    v |= (value & 0x0000ff00) << 8;
    //@ assert v == (\at(v, left_shift_24) | (unsigned long) ((value & 0x0000ff00) << 8));
    //@ ghost left_shift_8:

    v |= (value & 0x00ff0000) >> 8;
    //@ assert v == (\at(v, left_shift_8) | ((value & 0x00ff0000) >> 8));
    //@ ghost right_shift_8:

    v |= (value & 0xff000000) >> 24;
    //@ assert v == (\at(v, right_shift_8) | ((value & 0xff000000) >> 24));

    return v;
}

/*@
  @ ensures \result == (value & 0x000000ff);
  @*/
unsigned long filter_ff_union(unsigned long value) {
    union u {unsigned long vi; unsigned char c[sizeof(unsigned long)];};
    union v {unsigned long ni; unsigned char d[sizeof(unsigned long)];};
    union u un;
    union v vn;
    un.vi = value;

    //@ assert un.c[0] == (value & 0x000000ff);
    vn.d[0]=un.c[0];
    vn.d[1]=0;
    vn.d[2]=0;
    vn.d[3]=0;
    return (vn.ni);
}
