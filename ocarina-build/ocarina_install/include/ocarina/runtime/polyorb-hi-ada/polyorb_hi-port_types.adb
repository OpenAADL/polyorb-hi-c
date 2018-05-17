------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                P O L Y O R B _ H I . P O R T _ T Y P E S                 --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2017 ESA & ISAE.                       --
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
with PolyORB_HI.Utils; use PolyORB_HI.Utils;

package body PolyORB_HI.Port_Types is

   -------------------
   -- Internal_Code --
   -------------------

   function Internal_Code (P : Port_Type) return Unsigned_16 is
      function To_Internal_Code is new Ada.Unchecked_Conversion
        (Port_Type, Unsigned_16);
   begin
      return Swap_Bytes (To_Internal_Code (P));
   end Internal_Code;

   ------------------------
   -- Corresponding_Port --
   ------------------------

   function Corresponding_Port (I : Unsigned_16) return Port_Type is
      function To_Corresponding_Port is new Ada.Unchecked_Conversion
        (Unsigned_16, Port_Type);
   begin
      return To_Corresponding_Port (Swap_Bytes (I));
   end Corresponding_Port;

end PolyORB_HI.Port_Types;
