#include <string.h>
#include <assert.h>
#include <math.h>
#include <float.h>

#include "asn1crt.h"





int GetCharIndex(char ch, byte Set[], int setLen)
{
    int i=0;
    for(i=0; i<setLen; i++)
        if (ch == Set[i])
            return i;
    return 0;
}



void ByteStream_Init(ByteStream* pStrm, byte* buf, long count) 
{
    pStrm->count = count;
    pStrm->buf = buf;
    memset(pStrm->buf,0x0,(size_t)count);
    pStrm->currentByte = 0;
    pStrm->EncodeWhiteSpace = FALSE;
}

void ByteStream_AttachBuffer(ByteStream* pStrm, unsigned char* buf, long count)
{
    pStrm->count = count;
    pStrm->buf = buf;
    pStrm->currentByte = 0;
}

asn1SccSint ByteStream_GetLength(ByteStream* pStrm)
{
    return pStrm->currentByte;
}

#if WORD_SIZE==8
const asn1SccUint64 ber_aux[] = { 
    0xFF,
    0xFF00,
    0xFF0000,
    0xFF000000,
    0xFF00000000ULL,
    0xFF0000000000ULL,
    0xFF000000000000ULL,
    0xFF00000000000000ULL };
#else
const asn1SccUint32 ber_aux[] = {
    0xFF,
    0xFF00,
    0xFF0000,
    0xFF000000 };
#endif



asn1SccUint int2uint(asn1SccSint v) {
    asn1SccUint ret = 0;
    if (v < 0) {
        ret = (asn1SccUint)(-v - 1);
        ret = ~ret;
    }
    else {
        ret = (asn1SccUint)v;
    };
    return ret;
}

asn1SccSint uint2int(asn1SccUint v, int uintSizeInBytes) {
    int i;
    asn1SccUint tmp = 0x80;
    flag bIsNegative = (v & (tmp << ((uintSizeInBytes - 1) * 8)))>0;
    if (!bIsNegative)
        return (asn1SccSint)v;
    for (i = WORD_SIZE - 1; i >= uintSizeInBytes; i--)
        v |= ber_aux[i];
    return -(asn1SccSint)(~v) - 1;
}



/*

#######                                      ###
#     # #####       # ######  ####  #####     #  #####  ###### #    # ##### # ###### # ###### #####
#     # #    #      # #      #    #   #       #  #    # #      ##   #   #   # #      # #      #    #
#     # #####       # #####  #        #       #  #    # #####  # #  #   #   # #####  # #####  #    #
#     # #    #      # #      #        #       #  #    # #      #  # #   #   # #      # #      #####
#     # #    # #    # #      #    #   #       #  #    # #      #   ##   #   # #      # #      #   #
####### #####   ####  ######  ####    #      ### #####  ###### #    #   #   # #      # ###### #    #

Object Identifier

*/

void ObjectIdentifier_Init(Asn1ObjectIdentifier *pVal) {
	int i;
	for (i = 0; i < OBJECT_IDENTIFIER_MAX_LENGTH; i++) {
		pVal->values[i] = 0;
	}
	pVal->nCount = 0;
}

flag ObjectIdentifier_isValid(const Asn1ObjectIdentifier *pVal) {
	return (pVal->nCount >= 2) && (pVal->values[0] <= 2) && (pVal->values[1] <= 39);
}

flag RelativeOID_isValid(const Asn1ObjectIdentifier *pVal) {
	return pVal->nCount > 0;
}

flag ObjectIdentifier_equal(const Asn1ObjectIdentifier *pVal1, const Asn1ObjectIdentifier *pVal2) {
	int i;
	if ((pVal1 != NULL) && (pVal2 != NULL) && pVal1->nCount == pVal2->nCount && pVal1->nCount <= OBJECT_IDENTIFIER_MAX_LENGTH) {
		flag ret = true;
		for (i = 0; i < pVal1->nCount && ret; i++)
		{
			ret = (pVal1->values[i] == pVal2->values[i]);
		}
		return ret;
	}
	else {
		return FALSE;
	}
}




