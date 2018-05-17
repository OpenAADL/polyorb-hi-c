------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                                  M P C                                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--    Copyright (C) 2007-2009 Telecom ParisTech, 2010-2018 ESA & ISAE.      --
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
with PolyORB_HI_Generated.Deployment;

package body MPC is

   use PolyORB_HI.Output;
   use PolyORB_HI_Generated.Deployment;

   The_Observed_Object : Record_Type_Impl := (10, 13, 16);

   function Get_Node return String;
   pragma Inline (Get_Node);

   function Image (X : Component_Type) return String;
   pragma Inline (Image);

   function Image (R : Record_Type_Impl) return String;
   pragma Inline (Image);

   --------------
   -- Get_Node --
   --------------

   function Get_Node return String is
   begin
      return Node_Image (My_Node);
   end Get_Node;

   -----------
   -- Image --
   -----------

   function Image (X : Component_Type) return String is
      Img   : constant String := Component_Type'Image (X);
      Img_T : constant String (Img'First + 1 .. Img'Last)
        := Img (Img'First + 1 .. Img'Last);
   begin
      if Img (Img'First) /= ' ' then
         return Img;
      else
         return Img_T;
      end if;
   end Image;

   -----------
   -- Image --
   -----------

   function Image (R : Record_Type_Impl) return String is
   begin
      return "(" & Image (R.X) & ", " & Image (R.Y) & ", " & Image (R.Z) & ")";
   end Image;

   ------------
   -- Update --
   ------------

   procedure Update
     (Update_Value :        Record_Type_Impl;
      X            : in out Component_Type;
      Y            : in out Component_Type;
      Z            : in out Component_Type)
   is
   begin
      Put_Line ("Updating the local object.");
      X := Update_Value.X;
      Y := Update_Value.Y;
      Z := Update_Value.Z;
      Put_Line ("Local object updated. New value " & Image (Update_Value));
   end Update;

   ----------
   -- Read --
   ----------

   procedure Read
     (Read_Value :    out Record_Type_Impl;
      X          : in out Component_Type;
      Y          : in out Component_Type;
      Z          : in out Component_Type)
   is
      pragma Warnings (Off, X);
      pragma Warnings (Off, Y);
      pragma Warnings (Off, Z);
      --  To kill warning "mode could be "in" instead of "in out"

   begin
      Put_Line ("Reading the local object");
      Read_Value := (X, Y, Z);
      Put_Line ("Read value " & Image (Read_Value));
   end Read;

   --------------------
   -- Observe_Object --
   --------------------

   procedure Observe_Object (Data_Source : out Record_Type_Impl) is
   begin
      Data_Source := The_Observed_Object;
      Put_Line ("Order to set the local object to " & Image (Data_Source));
      The_Observed_Object.X := The_Observed_Object.X + 1;
      The_Observed_Object.Y := The_Observed_Object.Y + 2;
      The_Observed_Object.Z := The_Observed_Object.Z + 3;
   end Observe_Object;

   ------------------------
   -- Watch_Object_Value --
   ------------------------

   procedure Watch_Object_Value (Read_Value : Record_Type_Impl) is
   begin
      Put_Line ("Watched " & Image (Read_Value));
   end Watch_Object_Value;

end MPC;
