------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                  P O L Y O R B _ H I . M E S S A G E S                   --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--    Copyright (C) 2006-2009 Telecom ParisTech, 2010-2018 ESA & ISAE.      --
--                                                                          --
-- PolyORB-HI is free software; you can redistribute it and/or modify under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion. PolyORB-HI is distributed in the hope that it will be useful, but  --
-- WITHOUT ANY WARRANTY; without even the implied warranty of               --
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                     --
--                                                                          --
-- As a special exception under Section 7 of GPL version 3, you are granted --
-- additional permissions described in the GCC Runtime Library Exception,   --
-- version 3.1, as published by the Free Software Foundation.               --
--                                                                          --
-- You should have received a copy of the GNU General Public License and    --
-- a copy of the GCC Runtime Library Exception along with this program;     --
-- see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    --
-- <http://www.gnu.org/licenses/>.                                          --
--                                                                          --
--              PolyORB-HI/Ada is maintained by the TASTE project           --
--                      (taste-users@lists.tuxfamily.org)                   --
--                                                                          --
------------------------------------------------------------------------------

--  Definition of the messages exchanged by PolyORB HI partitions

with PolyORB_HI.Streams;
with PolyORB_HI_Generated.Deployment;

package PolyORB_HI.Messages is

   pragma Preelaborate;

   use PolyORB_HI.Streams;
   use PolyORB_HI_Generated.Deployment;

   type Message_Type is private;
   --  Base type of messages exchanged between nodes

   Message_Length_Size : constant := 2;
   --  Number of bytes to store a message size

   Header_Size : constant := Message_Length_Size + 2;
   --  Size of the header (see the documentation in the body for
   --  details on the header internal structure).

   PDU_Size : constant := Header_Size + (Max_Payload_Size / 8) + 1;
   --  Maximum size of a request

   subtype Message_Size_Buffer is Stream_Element_Array
     (1 .. Message_Length_Size);
   --  The sub-buffer that holds the message length

   function To_Length (B : Message_Size_Buffer) return Stream_Element_Count;
   function To_Buffer (L : Stream_Element_Count) return Message_Size_Buffer
     with Pre => (L < 2**16 -1); -- XXX Provide a better bound for L
   --  Conversion functions to store/extract a length in/from a sub-buffer.

   function Size (M : Message_Type) return Stream_Element_Count;
   --  Return the size of the message type, as the sum of the header
   --  plus payload

   procedure Read
     (Stream : in out Message_Type;
      Item   :    out Stream_Element_Array;
      Last   :    out Stream_Element_Offset)
     with Pre => (Valid (Stream));
   --  Move Item'Length stream elements from the specified stream to
   --  fill the array Item. The index of the last stream element
   --  transferred is returned in Last. Last is less than Item'Last
   --  only if the end of the stream is reached.

   procedure Write
     (Stream : in out Message_Type;
      Item   :        Stream_Element_Array)
     with Pre => (Valid (Stream));
   --  Append Item to the specified stream

   procedure Reallocate (M : in out Message_Type);
   --  Reset M

   function Sender (M : Message_Type) return Entity_Type
       with Pre => (Valid (M));
   function Sender (M : Stream_Element_Array) return Entity_Type;
   --  Return the sender of the message M

   procedure Encapsulate
     (Message : Message_Type;
      From    : Entity_Type;
      Entity  : Entity_Type;
      R : in out Polyorb_Hi.Streams.Stream_Element_Array)
     with Pre => (Valid (Message));
   --  Return a byte array including a two byte header (length and
   --  originator entity) and Message payload.

   function Valid (Message : Message_Type) return Boolean;

private

   subtype PDU_Index is Stream_Element_Count range 0 .. PDU_Size;
   subtype PDU is Stream_Element_Array (1 .. PDU_Index'Last);

   Empty_PDU : constant PDU := (others => 0);

   type Message_Type is record
      Content : PDU := Empty_PDU;
      First   : PDU_Index := 1;
      Last    : PDU_Index := 0;
   end record;

   function Size (M : Message_Type) return Stream_Element_Count is
     (M.Last + Header_Size);

   function Valid (Message : Message_Type) return Boolean is
      (Message.First >= Message.Content'First);
   --  The following part cannot be correct in the case Message is
   --  not initialized, see defaults for Message_Type
   --    and then Message.First <= Message.Last

   pragma Inline (To_Length);
   pragma Inline (To_Buffer);
   pragma Inline (Sender);

end PolyORB_HI.Messages;
