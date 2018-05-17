------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                              M A N A G E R                               --
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

--  $Id: manager.ads 6273 2009-03-25 17:36:51Z lasnier $

--  Implementation routines for the Flight manager application

with PolyORB_HI_Generated.Types;      use PolyORB_HI_Generated.Types;
with PolyORB_HI_Generated.Deployment; use PolyORB_HI_Generated.Deployment;

package Manager is

   --  Landing_Gear_T thread

   procedure On_Req (Entity : Entity_Type);
   procedure On_Dummy_In (Entity : Entity_Type);

   --  HCI_T thread

   procedure On_Stall_Warning
     (Entity        : Entity_Type;
      Stall_Warning : Ravenscar_Integer);
   procedure On_Engine_Failure (Entity : Entity_Type);
   procedure On_Gear_Cmd (Entity : Entity_Type);
   procedure On_Gear_Ack (Entity : Entity_Type);

   --  Operator_T thread

   procedure On_Operator (Entity : Entity_Type);

   --  Sensor_Sim_T.RS thread

   procedure On_Sensor_Sim (Entity : Entity_Type);

   --  Stall_Monitor_T.RS

   procedure On_Stall_Monitor (Entity : Entity_Type);

end Manager;
