------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                     W E A P O N _ S E L E C T I O N                      --
--                                                                          --
--                                 S p e c                                  --
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

with PolyORB_HI_Generated.Types;      use PolyORB_HI_Generated.Types;
with PolyORB_HI_Generated.Deployment; use PolyORB_HI_Generated.Deployment;

package Weapon_Selection is

   procedure On_Weapon_Select_Request (Entity : Entity_Type;
                                       Weapon_Select_Request : RAP_Int_32);

   procedure On_Quantity_Select_Request (Entity : Entity_Type;
                                         Quantity_Select_Request : RAP_Int_32);

   procedure On_Interval_Select_Request (Entity : Entity_Type;
                                         Interval_Select_Request : RAP_Int_32);

   procedure On_Auto_CCIP_Toggle (Entity : Entity_Type);

end Weapon_Selection;
