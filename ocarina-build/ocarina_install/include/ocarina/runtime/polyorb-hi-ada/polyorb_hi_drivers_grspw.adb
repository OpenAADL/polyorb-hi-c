------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--             P O L Y O R B _ H I _ D R I V E R S _ G R S P W              --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                   Copyright (C) 2012-2015 ESA & ISAE.                    --
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

with Ada.Unchecked_Conversion;
with Interfaces;

with SpaceWire.HLInterface;

with PolyORB_HI.Output;
with PolyORB_HI.Messages;

with PolyORB_HI_Generated.Transport;

with POHICDRIVER_SPACEWIRE; use POHICDRIVER_SPACEWIRE;

--  This package provides support for the GRSPW device driver as
--  defined in the GRSPW AADLv2 model.

package body PolyORB_HI_Drivers_GRSPW is

   task body Idle_Task is
      --  This Idle task is present to ensure the leon processor is
      --  never put idle, which would cause the processor to never be
      --  awakened by external events.
      --  XXX Check whether this is still necessary
   begin
      loop
         null;
      end loop;
   end Idle_Task;

   pragma Suppress (Elaboration_Check, PolyORB_HI_Generated.Transport);
   --  We do not want a pragma Elaborate_All to be implicitely
   --  generated for Transport.

   use Interfaces;
   use PolyORB_HI.Messages;
   use PolyORB_HI.Utils;
   use PolyORB_HI.Output;
   use type System.Address;

   type Spacewire_Conf_T_Acc is access all Spacewire_Conf_T;
   function To_Spacewire_Conf_T_Acc is new Ada.Unchecked_Conversion
     (System.Address, Spacewire_Conf_T_Acc);

   type Node_Record is record
      --  SpaceWire is a simple protocol, we use one core to send,
      --  another to receive.

      SpaceWire_Core_Send : SpaceWire.HLInterface.SpaceWire_Device;
      SpaceWire_Core_Receive : SpaceWire.HLInterface.SpaceWire_Device;
      SpaceWire_Config : POHICDRIVER_SPACEWIRE.Spacewire_Conf_T;
   end record;

   Nodes : array (Node_Type) of Node_Record;

   subtype AS_Full_Stream is
     SpaceWire.HLInterface.Receiver_Packet_Type (1 .. PDU_Size);
   subtype Full_Stream is Stream_Element_Array (1 .. PDU_Size);

   function To_PO_HI_Full_Stream is new Ada.Unchecked_Conversion
     (AS_Full_Stream, Full_Stream);

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize (Name_Table : PolyORB_HI.Utils.Naming_Table_Type) is
      Success : Boolean;

   begin
      SpaceWire.HLInterface.Initialize (Success);
      if not Success then
         Put_Line (Normal,
                   "Initialization failure: cannot find SpaceWire cores");
      end if;

      for J in Name_Table'Range loop

	 if Name_Table (J).Variable = System.Null_Address then
	    --  The structure of the location information is
	    --     "spacewire Sender_Core_id Receiver_Core_Id"

	    declare
	       S : constant String := PolyORB_HI.Utils.To_String
		 (Name_Table (J).Location);
	       First, Last : Integer;

	    begin
	       --  First parse the prefix "spacewire"

	       First := S'First;
	       Last := Parse_String (S, First, ' ');

	       if S (First .. Last) /= "spacewire" then
		  raise Program_Error with "Invalid configuration";
	       end if;

	       --  Then the sender_core_id

	       First := Last + 2;
	       Last := Parse_String (S, First, ' ');
	       Nodes (J).SpaceWire_Core_Send
		 := SpaceWire.HLInterface.SpaceWire_Device'Value
		 (S (First .. Last));

	       --  Finally the receiver_core_id

	       First := Last + 2;
	       Last := Parse_String (S, First, ' ');
	       Nodes (J).SpaceWire_Core_Receive
		 := SpaceWire.HLInterface.SpaceWire_Device'Value
		 (S (First .. Last));

	       SpaceWire.HLInterface.Set_Node_Address
		 (Nodes (J).SpaceWire_Core_Send,
		  Interfaces.Unsigned_8 (Nodes (J).SpaceWire_Core_Receive));
	    end;
	 else
	    Nodes (J).SpaceWire_Config := To_Spacewire_Conf_T_Acc
	      (Name_Table (J).Variable).all;
            Put_Line (Normal, "Device: "
			& Nodes (J).SpaceWire_Config.devname);

	    --  Translate the device name into a SpaceWire_Device

	    if Nodes (J).SpaceWire_Config.Devname (1 .. 15)
	      /= "/dev/grspwrasta"
	    then
	       Put_Line ("invalid device name");

	    else
	       --  We assume the device name to be "/dev/grspwrastaX"
	       --  with X in 0 .. 2. We need to move X to the 1 .. 3
	       --  range.

	       Nodes (J).SpaceWire_Core_Send
		 := SpaceWire.HLInterface.SpaceWire_Device
		 (Integer'Value
		    (Nodes (J).SpaceWire_Config.Devname (16 .. 16)) + 1);

	       SpaceWire.HLInterface.Set_Node_Address
		 (Nodes (J).SpaceWire_Core_Send,
		  Interfaces.Unsigned_8 (Nodes (J).SpaceWire_Core_Receive));

	       --  When using ASN.1 configuration variable, we use the
	       --  same core for sending and receiving.

	       Nodes (J).SpaceWire_Core_Receive
		 := Nodes (J).SpaceWire_Core_Send;
	    end if;
	 end if;
      end loop;

      pragma Debug (Put_Line (Normal, "Initialization of SpaceWire subsystem"
                                & " is complete"));
   end Initialize;

   -------------
   -- Receive --
   -------------

   procedure Receive is
      use type SpaceWire.HLInterface.Receiver_Packet_Size_Type;
      SEA       : AS_Full_Stream;
      SEO       : SpaceWire.HLInterface.Receiver_Packet_Size_Type;

   begin
      Main_Loop : loop
         Put_Line ("Using user-provided GRSPW stack to receive");
         Put_Line ("Waiting on Spacewire core #" &
                     Nodes (My_Node).Spacewire_Core_Receive'Img);

         --  SpaceWire is packet oriented, we fetch in one call all
         --  required information.

         SpaceWire.HLInterface.Receive
           (Nodes (My_Node).Spacewire_Core_Receive, SEA, SEO);

         Put_Line
           (Normal,
            "Received"
              & SpaceWire.HLInterface.Receiver_Packet_Size_Type'Image (SEO)
              & " bytes on core "
              & Nodes (My_Node).SpaceWire_Core_Receive'Img);

         --  Deliver to the peer handler

         PolyORB_HI_Generated.Transport.Deliver
           (Corresponding_Entity
              (Unsigned_8 (SEA (Message_Length_Size + 1))),
            To_PO_HI_Full_Stream (SEA)
              (1 .. Stream_Element_Offset (SEO)));
      end loop Main_Loop;
   end Receive;

   ----------
   -- Send --
   ----------

   function Send
     (Node    : Node_Type;
      Message : Stream_Element_Array;
      Size    : Stream_Element_Offset)
     return Error_Kind
   is
      --  Note: we cannot cast both array types using
      --  Ada.Unchecked_Conversion because they are unconstrained
      --  types. We cannot either use direct casting because component
      --  types are incompatible. The only time efficient manner to do
      --  the casting is to use representation clauses.

      Msg : SpaceWire.HLInterface.Transmitter_Data_Packet_Type
        (1 .. SpaceWire.HLInterface.Transmitter_Packet_Data_Size_Type (Size));
      pragma Import (Ada, Msg);
      for Msg'Address use Message'Address;

   begin
      Put_Line ("Using user-provided SpaceWire stack to send");
      Put_Line ("Sending through Spacewire core #"
                  & Nodes (My_Node).SpaceWire_Core_Send'Img
                  & " to address"
                  & Nodes (Node).SpaceWire_Core_Receive'Img);

      SpaceWire.HLInterface.Send
        (Device   => Nodes (My_Node).SpaceWire_Core_Send,
         Address  =>
           Interfaces.Unsigned_8 (Nodes (Node).SpaceWire_Core_Receive),
         Data     => Msg,
         Blocking => False);

      return Error_Kind'(Error_None);
      --  Note: we have no way to no there was an error here
   end Send;

end PolyORB_HI_Drivers_GRSPW;
