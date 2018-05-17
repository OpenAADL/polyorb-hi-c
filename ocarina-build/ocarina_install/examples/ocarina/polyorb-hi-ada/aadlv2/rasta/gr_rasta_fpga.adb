------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                        G R _ R A S T A _ F P G A                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2015 ESA & ISAE.                       --
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

--  This package provides support for the GR_RASTA_FPGA device driver
--  as defined in the GR_RASTA_FPGA AADLv2 model.

package body GR_RASTA_FPGA is

   use PolyORB_HI.Utils;
   use PolyORB_HI.Output;

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize (Name_Table : PolyORB_HI.Utils.Naming_Table_Type) is
      pragma Unreferenced (Name_Table);
   begin
      Put_Line (Normal, "Initialization of SpaceWire subsystem"
                  & " is complete");
   end Initialize;

   -------------
   -- Receive --
   -------------

   procedure Receive is
   begin
      null;
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
   begin
      Put_Line ("Using user-provided FPGA stack to send");
      Put_Line ("Sending" & Stream_Element_Offset'Image (Size)
                  & " bytes");

      Dump (Message (Message'First .. Message'First + Size - 1), Normal);

      return Error_Kind'(Error_None);
      --  Note: we have no way to no there was an error here
   end Send;

end GR_RASTA_FPGA;
