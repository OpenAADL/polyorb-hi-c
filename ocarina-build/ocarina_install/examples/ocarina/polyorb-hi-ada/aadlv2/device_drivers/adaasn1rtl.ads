pragma Style_Checks (Off); -- turn off style checks
WITH Interfaces;
USE Interfaces;



WITH Unchecked_Conversion;

PACKAGE AdaAsn1RTL IS



   TYPE BIT IS mod 2**1;
   TYPE BitArray IS ARRAY (Natural  RANGE <>) OF BIT;
   for BitArray'Component_Size use 1;
   pragma Pack(BitArray);

   TYPE OctetBuffer IS ARRAY (Natural  RANGE <>) OF Unsigned_8;
   TYPE OctetBuffer_Ptr IS ACCESS ALL OctetBuffer;

   SUBTYPE Asn1Int IS Long_Long_Integer;
   SUBTYPE Asn1UInt IS Unsigned_64;
   MSBIT_ONE  : CONSTANT Asn1UInt := 2**(Asn1UInt'SIZE - 1);
   MSBYTE_FF  : CONSTANT Asn1UInt := Shift_Left(Asn1UInt(16#FF#), Asn1UInt'Size-8);


   TYPE Asn1SccSint IS NEW Asn1Int;

   SUBTYPE Octet IS BitArray(1..8);






   SUBTYPE Asn1Real IS LONG_Float;
   MantissaFactor : Asn1Real:=Asn1Real(Unsigned_64(2)**Asn1Real'Machine_Mantissa);


   TYPE OctetArray4 IS NEW OctetBuffer(1..4);
   TYPE OctetArray8 IS NEW OctetBuffer(1..8);



   TYPE Asn1Boolean IS NEW Boolean;
--   FOR Asn1Boolean'SIZE USE 32;




   SUBTYPE Flag IS Asn1Boolean;

   TYPE Asn1NullType IS NEW Character range Character'Val(0)..Character'Val(0);




   ERR_INSUFFICIENT_DATA          : CONSTANT INTEGER := 101;
   ERR_INCORRECT_PER_STREAM       : CONSTANT INTEGER := 102;
   ERR_INVALID_CHOICE_ALTERNATIVE : CONSTANT INTEGER := 103;
   ERR_INCORRECT_STREAM           : CONSTANT INTEGER := 104;
   ERR_INVALID_BER_FILE           : CONSTANT INTEGER := 201;
   ERR_BER_LENGTH_MISMATCH        : CONSTANT INTEGER := 202;
   ERR_BER_TAG_MISMATCH           : CONSTANT INTEGER := 203;



   GENERIC
      MAX : POSITIVE;
   PACKAGE BIT_STRING_PACKAGE IS
      TYPE BIT_STRING IS
         RECORD
            Length : Integer;
            Data  : BitArray (1 .. MAX);
         END RECORD;

      TYPE FIXED_BIT_STRING IS
         RECORD
            Data  : BitArray (1 .. MAX);
         END RECORD;

   END BIT_STRING_PACKAGE;



   TYPE ASN1_RESULT IS
      RECORD
         Success   : Boolean;
         ErrorCode : INTEGER := 0;
      END RECORD;



   TYPE BitStream
         (N : Integer) IS
      RECORD
         CurrentBit : Natural :=1;
         Data       : BitArray (1 .. N) := (1..N=>0);
      END RECORD;







   -- nBits 1 .. 7




   GENERIC
      MAX : POSITIVE;
      TYPE ELEMENT IS PRIVATE;
   PACKAGE SEQUENCE_OF_PACKAGE IS

      TYPE LIST IS ARRAY (Positive RANGE 1 .. MAX) OF ELEMENT;

      TYPE SEQUENCE_OF IS
         RECORD
            Length : Integer;
            Data  : LIST;
         END RECORD;

      TYPE FIXED_SEQUENCE_OF IS
         RECORD
            Data  : LIST;
         END RECORD;

   END SEQUENCE_OF_PACKAGE;






















END AdaAsn1RTL;

