------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                                 W O R K                                  --
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

with PolyORB_HI.Output;             use PolyORB_HI.Output;
with PolyORB_HI_Generated.Activity; use PolyORB_HI_Generated.Activity;

with Auxiliary;
with Production_Workload;

package body Work is

   Regular_Producer_Workload : constant Workload := 498;
   --  Approximatively 498 ms

   On_Call_Producer_Workload : constant Workload := 250;
   --  Approximatively 250 ms

   Activation_Condition : constant Auxiliary.Range_Counter := 2;
   --  The parameter used to query the condition for the activation of
   --  On_Call_Producer.

   --------------------------------
   -- Regular_Producer_Operation --
   --------------------------------

   procedure Regular_Producer_Operation (Entity : Entity_Type) is
   begin
      Put_Line ("Regular Producer: doing some work.");

      --  We execute the guaranteed level of workload

      Production_Workload.Small_Whetstone
        (Positive (Regular_Producer_Workload));

      --  Then, we check whether we need to farm excess load out to
      --  On_Call_Producer.

      if Auxiliary.Due_Activation (Activation_Condition) then

         --  If yes, then we issue the activation request with a
         --  parameter that determines the workload request. We
         --  perform this by sending the 'On_Call_Producer_Workload'
         --  to the 'Additional_Workload' OUT EVENT DATA port.

         Put_Line ("Sending extra work to  'On_Call_Producer':"
                   & Workload'Image (On_Call_Producer_Workload));

         Put_Value (Entity,
                    RavenscarExample_Regular_Producer_Interface'
                    (Additional_Workload,
                     On_Call_Producer_Workload));
      end if;

      --  We check whether we need to release Activation_Log

      if Auxiliary.Check_Due then
         --  If yes, then we trigger the OUT EVENT PORT
         --  'Handle_External_Interrupt'.

         Put_Line ("Signaling 'Activation Log Reader'");

         Put_Value (Entity,
                    RavenscarExample_Regular_Producer_Interface'
                    (Port => Handle_External_Interrupt));
      end if;

      --  Finally, we report nominal completion of the current
      --  activation.

      Put_Line ("Regular Producer: end of cyclic activation");
   end Regular_Producer_Operation;

   --------------------------------
   -- On_Call_Producer_Operation --
   --------------------------------

   procedure On_Call_Producer_Operation
     (Entity                         : Entity_Type;
      Additional_Workload_Depository : Workload)
   is
      pragma Unreferenced (Entity);
   begin
      Put_Line ("On Call Producer: doing some work.");

      --  We execute the required amount of excess workload

      Production_Workload.Small_Whetstone
        (Positive (Additional_Workload_Depository));

      --  Then we report nominal completion of current activation

      Put_Line ("On Call Producer: end of sporadic activation.");
   end On_Call_Producer_Operation;

end Work;
