------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                     P O L Y O R B _ H I . U T I L S                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--       Copyright (C) 2009 Telecom ParisTech, 2010-2018 ESA & ISAE.        --
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

with Ada.Task_Identification; use Ada.Task_Identification;

package body PolyORB_HI.Utils is

   ------------------
   -- To_HI_String --
   ------------------

   function To_HI_String (S : String) return HI_String is
      R : String (1 .. HI_String_Size) := (others => ' ');
   begin
      if S'Length < 1 then
         return HI_String'(S => R,
                           L => 0);

      elsif S'Length <= HI_String_Size then
         for J in 1 .. S'Length loop
            R (J) := S (S'First + (J - 1));

         end loop;

         --  XXX GNATProve GPL2014 cannot prove the code below, which
         --  appears equivalent, TBI
         --  R (1 .. S'Length) := S (S'First .. S'Last);

         return HI_String'(S => R,
                           L => S'Length);

      else
         R (1 .. HI_String_Size) := S (S'First .. S'First + HI_String_Size - 1);
         return HI_String'(S => R,
                           L => HI_String_Size);
      end if;

   end To_HI_String;

   ----------------
   -- Swap_Bytes --
   ----------------
   --  XXX check intrinsic __builtint_bswapXX

   function Swap_Bytes (B : Interfaces.Unsigned_16)
                       return Interfaces.Unsigned_16
   is
      use System;

   begin
      pragma Warnings (Off);
      --  Note: this is to disable a warning on the following test
      --  being always true/false on a node.

      if Default_Bit_Order = High_Order_First then
         return B;

         pragma Warnings (On);

      --  Little-endian case. We must swap the high and low bytes

      else
         return (B / 256) + (B mod 256) * 256;
      end if;
   end Swap_Bytes;

   ------------------
   -- Parse_String --
   ------------------

   function Parse_String (S : String; First : Integer; Delimiter : Character)
                         return Integer
   is
      Last : Integer := S'Last;
   begin
      for J in First .. S'Last loop
         if S (J) = Delimiter then
            Last := J - 1;
            exit;
         end if;
      end loop;

      return Last;
   end Parse_String;

   -----------------
   -- Set_Task_Id --
   -----------------

   Task_Id_Mapping : array (Entity_Type'Range) of Task_Id;

   procedure Set_Task_Id (My_Id : Entity_Type) is
   begin
      Task_Id_Mapping (My_Id) := Current_Task;
   end Set_Task_Id;

   -----------------
   -- Get_Task_Id --
   -----------------

   function Get_Task_Id return Entity_Type is
      My_Task_Id : constant Task_Id := Current_Task;
   begin
      for J in Task_Id_Mapping'Range loop
         if Task_Id_Mapping (J) = My_Task_Id then
            return J;
         end if;
      end loop;
      return Entity_Type'First;
   end Get_Task_Id;

end PolyORB_HI.Utils;
