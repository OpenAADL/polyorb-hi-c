------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--       P O L Y O R B _ H I _ D R I V E R S _ N A T I V E _ U A R T        --
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

With Ada.Exceptions;
with Ada.Streams;
with Ada.Unchecked_Conversion;
with Interfaces;

with GNAT.Serial_Communications;

with PolyORB_HI.Output;
with PolyORB_HI.Messages;

with PolyORB_HI_Generated.Transport;

--  This package provides support for the Native_UART device driver as
--  defined in the Native_UART AADLv2 model.

with System; use System;

with POHICDRIVER_UART; use POHICDRIVER_UART;

package body PolyORB_HI_Drivers_Native_UART is

   type Serial_Conf_T_Acc is access all POHICDRIVER_UART.Serial_Conf_T;
   function To_Serial_Conf_T_Acc is new Ada.Unchecked_Conversion
     (System.Address, Serial_Conf_T_Acc);

   To_GNAT_Baud_Rate : constant array (POHICDRIVER_UART.Baudrate_T) of
     GNAT.Serial_Communications.Data_Rate :=
     (B9600 => GNAT.Serial_Communications.B9600,
      B19200 => GNAT.Serial_Communications.B19200,
      B38400 => GNAT.Serial_Communications.B38400,
      B57600 => GNAT.Serial_Communications.B57600,
      B115200 => GNAT.Serial_Communications.B115200,
      B230400 => GNAT.Serial_Communications.B115200);
   --  XXX does not exist in GCC.4.4.4

   To_GNAT_Parity_Check : constant array (POHICDRIVER_UART.Parity_T) of
     GNAT.Serial_Communications.Parity_Check :=
     (Even => GNAT.Serial_Communications.Even,
      Odd => GNAT.Serial_Communications.Odd);

   To_GNAT_Bits : constant array (7 .. 8) of
     GNAT.Serial_Communications.Data_Bits :=
     (7 => GNAT.Serial_Communications.CS8,
      8 => GNAT.Serial_Communications.CS8);

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

      UART_Port   : GNAT.Serial_Communications.Serial_Port;
      UART_Config : Serial_Conf_T; --  ASN.1 Configuration variable
   end record;

   Nodes : array (Node_Type) of Node_Record;

   subtype AS_Message_Length_Stream is Ada.Streams.Stream_Element_Array
     (1 .. Message_Length_Size);
   subtype Message_Length_Stream is Stream_Element_Array
     (1 .. Message_Length_Size);

   subtype AS_Full_Stream is Ada.Streams.Stream_Element_Array (1 .. PDU_Size);
   subtype Full_Stream is Stream_Element_Array (1 .. PDU_Size);

   function To_PO_HI_Message_Length_Stream is new Ada.Unchecked_Conversion
     (AS_Message_Length_Stream, Message_Length_Stream);
   function To_PO_HI_Full_Stream is new Ada.Unchecked_Conversion
     (AS_Full_Stream, Full_Stream);

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize (Name_Table : PolyORB_HI.Utils.Naming_Table_Type) is
      Parity    : GNAT.Serial_Communications.Parity_Check;
      Use_ASN1 : Boolean := False;

   begin
      for J in Name_Table'Range loop
         if Name_Table (J).Variable = System.Null_Address then
            --  The structure of the location information is
            --     "serial DEVICE BAUDS DATA_BITS PARITY STOP_BIT"

            declare
               S : constant String := PolyORB_HI.Utils.To_String
                 (Name_Table (J).Location);
               Device_First, Device_Last : Integer;
               Bauds     : GNAT.Serial_Communications.Data_Rate;
               Bits      : GNAT.Serial_Communications.Data_Bits;
               Stop_Bits : GNAT.Serial_Communications.Stop_Bits_Number;

               First, Last : Integer;

            begin
               First := S'First;

               --  First parse the prefix "serial"

               Last := Parse_String (S, First, ' ');

               if S (First .. Last) /= "serial" then
                  raise Program_Error with "Invalid configuration";
               end if;

               --  Then, parse the device

               First := Last + 2;
               Last := Parse_String (S, First, ' ');
               Device_First := First;
               Device_Last := Last;

               --  Then, parse the baud rate

               First := Last + 2;
               Last := Parse_String (S, First, ' ');
               begin
                  Bauds := GNAT.Serial_Communications.Data_Rate'Value
                    ('B' & S (First .. Last));
               exception
                  when others =>
                     Put_Line (Normal, "Wrong baud rate: " & S (First .. Last));
                     raise;
               end;

               --  Then, parse the data bits

               First := Last + 2;
               Last := Parse_String (S, First, ' ');

               --  Note: on GNAT GPL 2008 and before, Data_Bits define
               --  the B8 and B7 enumerators; on GNAT GPL 2009 and after,
               --  Data_Bits define the CS8 and CS7 enumerators.

               if S (First) = '8' then
                  Bits := GNAT.Serial_Communications.CS8;
               elsif S (First) = '7' then
                  Bits := GNAT.Serial_Communications.CS7;
               else
                  raise Program_Error with "Wrong bits: " & S (First);
               end if;

               --  Then, parse the parity

               First := Last + 2;
               Last := Parse_String (S, First, ' ');

               if S (First) = 'N' then
                  Parity :=  GNAT.Serial_Communications.None;
               elsif S (First) = 'E' then
                  Parity :=  GNAT.Serial_Communications.Even;
               elsif S (First) = 'O' then
                  Parity :=  GNAT.Serial_Communications.Odd;
               else
                  raise Program_Error with "Wrong parity: " & S (First);
               end if;

               --  Finally, parse the stop_bits

               First := Last + 2;
               Last := Parse_String (S, First, ' ');

               if S (First) = '1' then
                  Stop_Bits :=  GNAT.Serial_Communications.One;
               elsif S (First) = '2' then
                  Stop_Bits :=  GNAT.Serial_Communications.Two;
               else
                  raise Program_Error with "Wrong stop bits: " & S (First);
               end if;

               GNAT.Serial_Communications.Open
                 (Port => Nodes (My_Node).UART_Port,
                  Name => GNAT.Serial_Communications.Port_Name
                    (S (Device_First .. Device_Last)));

               GNAT.Serial_Communications.Set
                 (Port      => Nodes (My_Node).UART_Port,
                  Rate      => Bauds,
                  Bits      => Bits,
                  Stop_Bits => Stop_Bits,
                  Parity    => Parity,
                  Block     => True);

            exception
               when others =>
                  Put_Line (Normal, "Initialization of UART subsystem dead");
            end;
         else
            --  We got an ASN.1 configuration variable, use it
            --  directly.
	    Use_ASN1 := True;
            Nodes (J).UART_Config := To_Serial_Conf_T_Acc
              (Name_Table (J).Variable).all;

         end if;
      end loop;

      GNAT.Serial_Communications.Open
	(Port => Nodes (My_Node).UART_Port,
	 Name => GNAT.Serial_Communications.Port_Name
	   (Nodes (My_Node).UART_Config.devname));

      if Nodes (My_Node).UART_Config.Use_Paritybit then
	 Parity := To_GNAT_Parity_Check
	   (Nodes (My_Node).UART_Config.Parity);
      else
	 Parity := GNAT.Serial_Communications.None;
      end if;

      Put_Line (Normal, " -> Using ASN.1: " & Use_ASN1'Img);
      Put_Line (Normal, "Device: " & Nodes (My_Node).UART_Config.devname);
      Put_Line (Normal, "  * Use Parity bits: "
		  & Nodes (My_Node).UART_Config.use_paritybit'Img);
      Put_Line (Normal, "  * Rate: "
		  & To_GNAT_Baud_Rate (Nodes (My_Node).UART_Config.Speed)'Img);
      Put_Line (Normal, "  * Parity: " & Parity'Img);
      Put_Line (Normal, "  * Bits: "
		  & To_GNAT_Bits
		  (Integer (Nodes (My_Node).UART_Config.Bits))'Img);

      GNAT.Serial_Communications.Set
	(Port   => Nodes (My_Node).UART_Port,
         Rate   => To_GNAT_Baud_Rate (Nodes (My_Node).UART_Config.Speed),
         Parity => Parity,
         Bits   => To_GNAT_Bits (Integer (Nodes (My_Node).UART_Config.Bits)),
         Block  => True);

      Put_Line (Normal, "Initialization of Native_UART subsystem is complete");
   end Initialize;

   -------------
   -- Receive --
   -------------

   procedure Receive is
      use type Ada.Streams.Stream_Element_Offset;

      SEL : AS_Message_Length_Stream;
      SEA : AS_Full_Stream;
      SEO : Ada.Streams.Stream_Element_Offset;
      Packet_Size : Ada.Streams.Stream_Element_Offset;
      Data_Received_Index : Ada.Streams.Stream_Element_Offset;
   begin

      Main_Loop : loop
         Put_Line ("Using user-provided Native_UART stack to receive");

         --  UART is a character-oriented protocol

         --  1/ Receive message length

         GNAT.Serial_Communications.Read
           (Nodes (My_Node).UART_Port, SEL, SEO);

         Packet_Size := Ada.Streams.Stream_Element_Offset
           (To_Length (To_PO_HI_Message_Length_Stream (SEL)));
         SEO := Packet_Size;

         SEA (1 .. Message_Length_Size) := SEL;

         Data_Received_Index := Message_Length_Size + 1;

         while Data_Received_Index <= Packet_Size + Message_Length_Size loop
            --  We must loop to make sure we receive all data

            GNAT.Serial_Communications.Read
              (Nodes (My_Node).UART_Port,
               SEA (Data_Received_Index .. SEO + 1),
               SEO);
            Data_Received_Index := 1 + SEO + 1;
         end loop;

         --  2/ Receive full message

         if SEO /= SEA'First - 1 then
            Put_Line
              (Normal,
               "UART received"
                 & Ada.Streams.Stream_Element_Offset'Image (SEO)
                 & " bytes");

            --  Deliver to the peer handler

            begin
               PolyORB_HI_Generated.Transport.Deliver
                 (Corresponding_Entity
                    (Unsigned_8 (SEA (Message_Length_Size + 1))),
                  To_PO_HI_Full_Stream (SEA)
                    (1 .. Stream_Element_Offset (SEO)));
            exception
               when E : others =>
                  Put_Line (Ada.Exceptions.Exception_Information (E));
            end;
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
      pragma Unreferenced (Node);

      --  We cannot cast both array types using
      --  Ada.Unchecked_Conversion because they are unconstrained
      --  types. We cannot either use direct casting because component
      --  types are incompatible. The only time efficient manner to do
      --  the casting is to use representation clauses.

      Msg : Ada.Streams.Stream_Element_Array
        (1 .. Ada.Streams.Stream_Element_Offset (Size));
      pragma Import (Ada, Msg);
      for Msg'Address use Message'Address;

   begin
      Put_Line ("Using user-provided UART stack to send");
      Put_Line ("Sending through UART "
                  & Nodes (My_Node).UART_Config.devname
                  & Size'Img & " bytes");

      GNAT.Serial_Communications.Write
        (Port   => Nodes (My_Node).UART_Port,
         Buffer => Msg);

      return Error_Kind'(Error_None);
      --  Note: we have no way to know there was an error here

   end Send;

end PolyORB_HI_Drivers_Native_UART;
