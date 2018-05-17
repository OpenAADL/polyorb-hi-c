------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                               E V E N T S                                --
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

package body Events is

   -----------------------------
   -- Delegate_External_Event --
   -----------------------------

   procedure Delegate_External_Event
     (Entity                        : Entity_Type;
      External_Interrupt_Depository : Interrupt_Counter)
   is
   begin
      Put_Line ("External Event Server: received an external interrupt");

      --  We record an entry in the Activation_Log buffer. We perform
      --  this by sending a data to the OUT DATA port
      --  'External_Interrupt'.

      Put_Value (Entity,
                 RavenscarExample_External_Event_Server_Interface'
                 (External_Interrupt,
                  External_Interrupt_Depository));

      --  Then we report nominal completion of current activation

      Put_Line ("External Event Server: end of sporadic activation.");
   end Delegate_External_Event;

end Events;
