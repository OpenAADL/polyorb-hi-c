------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                P O L Y O R B _ H I . S U S P E N D E R S                 --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--    Copyright (C) 2007-2009 Telecom ParisTech, 2010-2015 ESA & ISAE.      --
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

--  This package implements routines to suspend application tasks
pragma SPARK_Mode (Off);

with Ada.Real_Time;

with PolyORB_HI_Generated.Deployment;
pragma Elaborate_All (PolyORB_HI_Generated.Deployment);

package PolyORB_HI.Suspenders is

   use PolyORB_HI_Generated.Deployment;

   procedure Suspend_Forever;
   --  Suspends for ever each task that call it

   System_Startup_Time : Ada.Real_Time.Time := Ada.Real_Time.Time_First;
   --  Startup time of user tasks

   procedure Block_Task (Entity : Entity_Type);
   --  Block a task until Unblock_All_Tasks is called.

   procedure Unblock_All_Tasks;
   --  Unblocks all the tasks waiting on the suspension objects of
   --  Task_Suspension_Objects.

end PolyORB_HI.Suspenders;
