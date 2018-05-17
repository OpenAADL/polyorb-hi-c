------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--            P O L Y O R B _ H I _ D R I V E R S _ G R U A R T             --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                   Copyright (C) 2012-2015 ESA & ISAE.                    --
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

with PolyORB_HI.Errors;
with PolyORB_HI_Generated.Deployment;
with PolyORB_HI.Streams;
with PolyORB_HI.Utils;
with System;

package PolyORB_HI_Drivers_GRUART is

   use PolyORB_HI.Errors;
   use PolyORB_HI_Generated.Deployment;
   use PolyORB_HI.Streams;

   procedure Initialize (Name_Table : PolyORB_HI.Utils.Naming_Table_Type);

   procedure Receive;

   function Send
     (Node    : Node_Type;
      Message : Stream_Element_Array;
      Size    : Stream_Element_Offset)
     return Error_Kind;

   task Idle_Task is
      --  Dummy idle task to work around an issue in the GRSPW driver
      --  in gnatforleon: if no task executes, the node goes in sleep
      --  mode, and cannot be awaken when a packet comes in. This task
      --  simulates a constant workload to prevent the node to
      --  hibernate.

      pragma Priority (System.Priority'First);
   end Idle_Task;

end PolyORB_HI_Drivers_GRUART;
