------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--            P O L Y O R B _ H I _ D R I V E R S _ G R U A R T             --
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

With Interfaces;
with Ada.Unchecked_Conversion;

with Uart.Core; use type UART.Core.UART_Device;
with Uart.HLInterface;
with Uart.Streams;

with PolyORB_HI.Output;
with PolyORB_HI.Messages;

with PolyORB_HI_Generated.Transport;

--  This package provides support for the GRUART device driver as
--  defined in the GRUART AADLv2 model.

with System; use System;

with POHICDRIVER_UART; use POHICDRIVER_UART;

package body PolyORB_HI_Drivers_GRUART is

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

   type Serial_Conf_T_Acc is access all POHICDRIVER_UART.Serial_Conf_T;
   function To_Serial_Conf_T_Acc is new Ada.Unchecked_Conversion
     (System.Address, Serial_Conf_T_Acc);

   To_GNAT_Baud_Rate : constant array (POHICDRIVER_UART.Baudrate_T) of
     UART.HLInterface.Data_Rate :=
     (B9600 => UART.HLInterface.B9600,
      B19200 => UART.HLInterface.B19200,
      B38400 => UART.HLInterface.B38400,
      B57600 => UART.HLInterface.B57600,
      B115200 => UART.HLInterface.B115200,
      B230400 => UART.HLInterface.B115200);
   --  XXX does not exist in ORK+

   To_GNAT_Parity_Check : constant array (POHICDRIVER_UART.Parity_T) of
     UART.HLInterface.Parity_Check :=
     (Even => UART.HLInterface.Even,
      Odd => UART.HLInterface.Odd);

   To_GNAT_Bits : constant array (7 .. 8) of
     UART.HLInterface.Data_Bits :=
     (7 => UART.HLInterface.B8,
      8 => UART.HLInterface.B8);

   pragma Suppress (Elaboration_Check, PolyORB_HI_Generated.Transport);
   --  We do not want a pragma Elaborate_All to be implicitely
   --  generated for Transport.

   use Interfaces;
   use PolyORB_HI.Messages;
   use PolyORB_HI.Utils;
   use PolyORB_HI.Output;

   type Node_Record is record
      --  UART is a simple protocol, we use one port to send, assuming
      --  it can be used in full duplex mode.

      UART_Port   : Uart.HLInterface.Serial_Port;
      UART_Device : Uart.Core.UART_Device;
      UART_Config : Serial_Conf_T;
   end record;

   Nodes : array (Node_Type) of Node_Record;

   subtype AS_Message_Length_Stream is Uart.STreams.Stream_Element_Array
     (1 .. Message_Length_Size);
   subtype Message_Length_Stream is Stream_Element_Array
     (1 .. Message_Length_Size);

   subtype AS_Full_Stream is Uart.Streams.Stream_Element_Array (1 .. PDU_Size);
   subtype Full_Stream is Stream_Element_Array (1 .. PDU_Size);

   function To_PO_HI_Message_Length_Stream is new Ada.Unchecked_Conversion
     (AS_Message_Length_Stream, Message_Length_Stream);
   function To_PO_HI_Full_Stream is new Ada.Unchecked_Conversion
     (AS_Full_Stream, Full_Stream);

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize (Name_Table : PolyORB_HI.Utils.Naming_Table_Type) is
      Success : Boolean;
      Use_Asn1 : Boolean := False;
      Parity : UART.HLInterface.Parity_Check;

   begin
      Uart.HLInterface.Initialize (Success);
      if not Success then
	 Put_Line (Normal,
		   "Initialization failure: cannot find UART cores");
	 raise Program_Error;
      end if;

      for J in Name_Table'Range loop
	 if Name_Table (J).Variable = System.Null_Address then
	    Nodes (J).UART_Device
	      := Uart.Core.UART_Device'Value
	      (To_String (Name_Table (J).Location) (1 .. 1));

	    --  Note: we only consider the first half of the
	    --  configuration string.

	 else
	    Nodes (J).UART_Config := To_Serial_Conf_T_Acc
	      (Name_Table (J).Variable).all;
	    Use_Asn1 := True;
            Put_Line (Normal, "Device: " & Nodes (J).UART_Config.devname);

	    --  Translate the device name into an UART_Device

	    if Nodes (J).UART_Config.Devname (1 .. 14) /= "/dev/apburasta" then
	       Put_Line (Error, "invalid device name");

	    else
	       --  We assume the device name to be "/dev/apburastaX"
	       --  with X in 0 .. 2. We need to move X to the 1 .. 3
	       --  range.

	       Nodes (J).UART_Device
		 := UART.Core.UART_Device
		 (Integer'Value (Nodes (J).UART_Config.Devname (15 .. 15)) + 1);
	    end if;
	 end if;
      end loop;

      Put_Line (Normal, "Opening UART #"
                     & Nodes (My_Node).UART_Device'Img);

      Uart.HLInterface.Open (Port   => Nodes (My_Node).UART_Port,
			     Number => Nodes (My_Node).UART_Device);

      if not Use_Asn1 then
	 Put_Line (Normal, " -> Using default configuration");

	 Uart.HLInterface.Set (Port   => Nodes (My_Node).UART_Port,
			       Rate => Uart.HLInterface.B19200,
			       Block => True);
      else
	 Put_Line (Normal, " -> Using ASN.1 configuration");

	 if Nodes (My_Node).UART_Config.Use_Paritybit then
	    Parity := To_GNAT_Parity_Check (Nodes (My_Node).UART_Config.Parity);
	 else
	    Put_Line (Normal, "  * Use Parity bits: FALSE");
	    Parity := UART.HLInterface.None;
	 end if;

	 declare
	    use Uart.HLInterface;

	    Rate : constant Uart.HLInterface.Data_Rate
	      := To_GNAT_Baud_Rate (Nodes (My_Node).UART_Config.Speed);
	    Bits : constant Data_Bits
	      := To_GNAT_Bits (Integer (Nodes (My_Node).UART_Config.Bits));
	 begin
	    case Rate is
	       when B1200 =>
		  Put_Line (Normal, "  * Rate : B1200");
	       when B2400 =>
		  Put_Line (Normal, "  * Rate : B2400");
	       when B4800 =>
		  Put_Line (Normal, "  * Rate : B4800");
	       when B9600 =>
		  Put_Line (Normal, "  * Rate : B9600");
	       when B19200 =>
		  Put_Line (Normal, "  * Rate : B19200");
	       when B38400 =>
		  Put_Line (Normal, "  * Rate : B38400");
	       when B57600 =>
		  Put_Line (Normal, "  * Rate : B57600");
	       when B115200 =>
		  Put_Line (Normal, "  * Rate : B115200");
	    end case;

	    case Parity is
	       when None =>
		  Put_Line (Normal, "  * Parity: None");
	       when Odd =>
		  Put_Line (Normal, "  * Parity: Odd");
	       when Even =>
		  Put_Line (Normal, "  * Parity: Even");
	    end case;

	    case Bits is
	       when B8 =>
		  Put_Line (Normal, "  * Bits: B8");
	       when B7 =>
		  Put_Line (Normal, "  * Bits: B7");
	    end case;

	 end;

	 UART.HLInterface.Set
           (Port   => Nodes (My_Node).UART_Port,
	    Rate   => To_GNAT_Baud_Rate (Nodes (My_Node).UART_Config.Speed),
	    Parity => Parity,
	    Bits   => To_GNAT_Bits (Integer (Nodes (My_Node).UART_Config.Bits)),
	    Block  => True);
      end if;
      pragma Debug (Put_Line (Normal, "Initialization of UART subsystem"
                                & " is complete"));
   end Initialize;

   -------------
   -- Receive --
   -------------

   procedure Receive is
      use type Uart.Streams.Stream_Element_Offset;

      SEL : AS_Message_Length_Stream;
      SEA : AS_Full_Stream;
      SEO : Uart.Streams.Stream_Element_Offset;
      Packet_Size : Uart.Streams.Stream_Element_Offset;
      Data_Received_Index : Uart.Streams.Stream_Element_Offset;
   begin

      Main_Loop : loop
         Put_Line ("Using user-provided GRUART stack to receive");
         Put_Line ("Waiting on UART #"
                     & Nodes (My_Node).UART_Device'Img);

         --  UART is a character-oriented protocol

         --  1/ Receive message length

         Uart.HLInterface.Read (Nodes (My_Node).UART_Port, SEL, SEO);

         Packet_Size := Uart.Streams.Stream_Element_Offset
           (To_Length (To_PO_HI_Message_Length_Stream (SEL)));
         SEO := Packet_Size;

         SEA (1 .. Message_Length_Size) := SEL;

         Data_Received_Index := Message_Length_Size + 1;

         while Data_Received_Index <= Packet_Size + Message_Length_Size loop
            --  We must loop to make sure we receive all data

            Uart.HLInterface.Read (Nodes (My_Node).UART_Port,
                                   SEA (Data_Received_Index .. SEO + 1),
                                   SEO);
            Data_Received_Index := 1 + SEO + 1;
         end loop;

         --  2/ Receive full message

         if SEO /= SEA'First - 1 then
            Put_Line
              (Normal,
               "UART #"
                 & Nodes (My_Node).UART_Device'Img
                 & " received"
                 & Uart.Streams.Stream_Element_Offset'Image (SEO)
                 & " bytes");

            --  Deliver to the peer handler

            PolyORB_HI_Generated.Transport.Deliver
              (Corresponding_Entity
                 (Unsigned_8 (SEA (Message_Length_Size + 1))),
               To_PO_HI_Full_Stream (SEA)
                 (1 .. Stream_Element_Offset (SEO)));
         else
            Put_Line ("Got error");
         end if;
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
      --  We cannot cast both array types using
      --  Ada.Unchecked_Conversion because they are unconstrained
      --  types. We cannot either use direct casting because component
      --  types are incompatible. The only time efficient manner to do
      --  the casting is to use representation clauses.

      Msg : Uart.Streams.Stream_Element_Array
        (1 .. Uart.Streams.Stream_Element_Offset (Size));
      pragma Import (Ada, Msg);
      for Msg'Address use Message'Address;

   begin
      Put_Line ("Using user-provided UART stack to send");
      Put_Line ("Sending through UART #"
                  & Nodes (Node).UART_Device'Img
                  & Size'Img & " bytes");

      Uart.HLInterface.Write (Port   => Nodes (My_Node).UART_Port,
                              Buffer => Msg);

      return Error_Kind'(Error_None);
      --  Note: we have no way to know there was an error here
   end Send;

end PolyORB_HI_Drivers_GRUART;
