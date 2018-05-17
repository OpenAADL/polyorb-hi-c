------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                      T R A N S M I T T E R _ P K G                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--       Copyright (C) 2009 Telecom ParisTech, 2010-2015 ESA & ISAE.        --
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

--  $Id: transmitter_pkg.adb 6851 2009-07-22 12:37:17Z hugues $

with PolyORB_HI_Generated.Types;
with PolyORB_HI.Output;

package body Transmitter_Pkg is

   use PolyORB_HI_Generated.Types;
   use PolyORB_HI.Output;

   Seed : Integer_Type := 0;

   ---------------
   -- Send_Data --
   ---------------

   procedure Send_Data (Status : in out Software_Send_Data_Status) is
   begin
      Seed := Seed + 1;

      if Seed mod 3 = 0 then
         Put_Line ("Transmitter: Raise event data on Data_Source:"
                   & Integer_Type'Image (Seed));
         Put_Value (Status, (Data_Source, Seed));
      else
         Put_Line ("Transmitter: Do not raise any port");
      end if;
   end Send_Data;

end Transmitter_Pkg;
