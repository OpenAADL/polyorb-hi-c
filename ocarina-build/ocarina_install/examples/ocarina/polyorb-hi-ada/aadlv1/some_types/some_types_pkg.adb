------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                       S O M E _ T Y P E S _ P K G                        --
--                                                                          --
--                                 B o d y                                  --
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

with PolyORB_HI.Output;

package body Some_Types_Pkg is

   use PolyORB_HI.Output;
   use String_Type_Pkg;

   Boolean_Type_Var : Boolean_Type := False;
   Enum_Type_Var    : Enum_Type    := Enum_Type'First;
   Integer_Type_Var : Integer_Type := 0;
   Array_Type_I_Var : Array_Type_I := (1, 2, 3, 4);
   String_Array     : constant array (Integer range <>) of String_Type :=
     (To_Bounded_String ("Bounded string message"),
      To_Bounded_String ("Longer bounded string message"),
      To_Bounded_String ("Even longer bounded string message"),
      To_Bounded_String ("Very much longer bounded string message"));
   String_Array_Pos : Integer := String_Array'First;

   ------------------
   -- Emit_Boolean --
   ------------------

   procedure Emit_Boolean (Data_Source : out Boolean_Type) is
   begin
      Boolean_Type_Var := not Boolean_Type_Var;
      Data_Source := Boolean_Type_Var;
      Put_Line
        ("***** Emitting Boolean_Type: " & Boolean_Type'Image (Data_Source));
   end Emit_Boolean;

   ---------------------
   -- Receive_Boolean --
   ---------------------

   procedure Receive_Boolean (Data_Sink : in Boolean_Type) is
   begin
      Put_Line
        ("***** Received Boolean_Type: " & Boolean_Type'Image (Data_Sink));
   end Receive_Boolean;

   ---------------
   -- Emit_Enum --
   ---------------

   procedure Emit_Enum (Data_Source : out Enum_Type) is
   begin
      if Enum_Type_Var /= Enum_Type'Last then
         Enum_Type_Var := Enum_Type'Succ (Enum_Type_Var);
      else
         Enum_Type_Var := Enum_Type'First;
      end if;
      Data_Source := Enum_Type_Var;
      Put_Line
        ("***** Emitting Enum_Type: " & Enum_Type'Image (Data_Source));
   end Emit_Enum;

   ------------------
   -- Receive_Enum --
   ------------------

   procedure Receive_Enum (Data_Sink : in Enum_Type) is
   begin
      Put_Line
        ("***** Received Enum_Type: " & Enum_Type'Image (Data_Sink));
   end Receive_Enum;

   ------------------
   -- Emit_Integer --
   ------------------

   procedure Emit_Integer (Data_Source : out Integer_Type) is
   begin
      Integer_Type_Var := Integer_Type_Var + 1;
      Data_Source := Integer_Type_Var;
      Put_Line
        ("***** Emitting Integer_Type: " & Integer_Type'Image (Data_Source));
   end Emit_Integer;

   ---------------------
   -- Receive_Integer --
   ---------------------

   procedure Receive_Integer (Data_Sink : in Integer_Type) is
   begin
      Put_Line
        ("***** Received Integer_Type: " & Integer_Type'Image (Data_Sink));
   end Receive_Integer;

   ----------------
   -- Emit_Array --
   ----------------

   procedure Emit_Array (Data_Source : out Array_Type_I) is
   begin
      Data_Source := Array_Type_I_Var;
      Array_Type_I_Var := (Array_Type_I_Var (2),
                           Array_Type_I_Var (3),
                           Array_Type_I_Var (4),
                           Array_Type_I_Var (1));
      Put_Line
        ("***** Emitting Array : ("
           & Integer_Type'Image (Data_Source (1))
           & ", " & Integer_Type'Image (Data_Source (2))
           & ", " & Integer_Type'Image (Data_Source (3))
           & ", " & Integer_Type'Image (Data_Source (4))
           & ")");
   end Emit_Array;

   -------------------
   -- Receive_Array --
   -------------------

   procedure Receive_Array (Data_Sink : in Array_Type_I) is
   begin
      Put_Line
        ("***** Receivinng Array : ("
           & Integer_Type'Image (Data_Sink (1))
           & ", " & Integer_Type'Image (Data_Sink (2))
           & ", " & Integer_Type'Image (Data_Sink (3))
           & ", " & Integer_Type'Image (Data_Sink (4))
           & ")");
   end Receive_Array;

   -----------------
   -- Emit_String --
   -----------------

   procedure Emit_String (Data_Source : out String_Type) is
   begin
      Data_Source := String_Array (String_Array_Pos);

      if String_Array_Pos < String_Array'Last then
         String_Array_Pos := String_Array_Pos + 1;
      else
         String_Array_Pos := String_Array'First;
      end if;

      Put_Line
        ("***** Emitting String_Type: " & To_String (Data_Source));
   end Emit_String;

   --------------------
   -- Receive_String --
   --------------------

   procedure Receive_String (Data_Sink : in String_Type) is
   begin
      Put_Line
        ("***** Received String_Type: """ & To_String (Data_Sink) & """");
   end Receive_String;

end Some_Types_Pkg;
