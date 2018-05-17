------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                                 L O G S                                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--    Copyright (C) 2008-2009 Telecom ParisTech, 2010-2015 ESA & ISAE.      --
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

with Ada.Real_Time;                 use  Ada.Real_Time;

with PolyORB_HI.Suspenders;         use PolyORB_HI.Suspenders;
with PolyORB_HI.Output;             use PolyORB_HI.Output;
with PolyORB_HI_Generated.Types;    use PolyORB_HI_Generated.Types;
with PolyORB_HI_Generated.Activity; use PolyORB_HI_Generated.Activity;

with Production_Workload;

package body Logs is

   Load : constant Workload := 125;
   --  Approximatively 125 ms

   Old_Interrupt_Counter : Interrupt_Counter := -1;

   ---------------
   -- On_Signal --
   ---------------

   procedure On_Signal (Entity : Entity_Type) is
      Interrupt_Arrival_Counter : Interrupt_Counter;
      Interrupt_Arrival_Time    : Ada.Real_Time.Time;
   begin
      if Get_Count
        (Entity,
         Activation_Log_Reader_Port_Type'
         (External_Interrupt_Depository)) /= -1
      then
         Put_Line ("Activation Log Reader: do some work.");

         --  We perform some work

         Production_Workload.Small_Whetstone (Positive (Load));

         --  Then we read into the Activation_Log buffer. We use this
         --  by reading the value sent to the IN DATA port
         --  'External_Interrupt_Depository' of the
         --  'Activation_Log_Reader' thread.

         Interrupt_Arrival_Counter := Get_Value
           (Entity,
            Activation_Log_Reader_Port_Type'(External_Interrupt_Depository))
           .External_Interrupt_Depository_DATA;

         Interrupt_Arrival_Time := Get_Time_Stamp
           (Entity,
            Activation_Log_Reader_Port_Type'(External_Interrupt_Depository));

         if Interrupt_Arrival_Counter /= Old_Interrupt_Counter then

            Put_Line ("Read external new interruption:"
                      & Interrupt_Counter'Image (Interrupt_Arrival_Counter)
                      & ". Arrived at ["
                      & Duration'Image
                      (To_Duration
                       (Interrupt_Arrival_Time - System_Startup_Time))
                      & "]");

            Old_Interrupt_Counter := Interrupt_Arrival_Counter;
         else
            Put_Line ("Activation Log Reader: no new interrupts.");
         end if;

         --  And finally we report nominal completion of current
         --  activation.

         Put_Line ("Activation Log Reader: end of parameterless sporadic"
                   & " activation.");
      else
         Put_Line ("Activation Log Reader: no new interrupts.");
      end if;
   end On_Signal;

end Logs;
