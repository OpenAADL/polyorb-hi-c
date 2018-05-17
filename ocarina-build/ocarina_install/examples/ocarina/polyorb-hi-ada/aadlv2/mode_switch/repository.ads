------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                           R E P O S I T O R Y                            --
--                                                                          --
--                                 S p e c                                  --
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

with PolyORB_HI_Generated.Types;      use PolyORB_HI_Generated.Types;
with PolyORB_HI_Generated.Activity;   use PolyORB_HI_Generated.Activity;
with PolyORB_HI_Generated.Deployment; use PolyORB_HI_Generated.Deployment;

package Repository is

   procedure Init_Raiser;
   procedure Init_Worker;

   procedure Raiser (M : out Simple_Type);
   --  Raise a message M

   procedure Normal_Handler (M : Simple_Type);
   procedure Emergency_Handler (M : Simple_Type);
   procedure Lazy_Handler (M : Simple_Type);
   procedure CE_Normal_Handler
     (Entity : Entity_Type;
      P      : ModesC_Worker_Impl_Port_Type);
   procedure CE_Emergency_Handler
     (Entity : Entity_Type;
      P      : ModesC_Worker_Impl_Port_Type);
   procedure CE_Lazy_Handler
     (Entity : Entity_Type;
      P      : ModesC_Worker_Impl_Port_Type);
   --  Handle a received message

   procedure Drive (Entity : Entity_Type);
   --  Raise an event depending on the cycle number
end Repository;
