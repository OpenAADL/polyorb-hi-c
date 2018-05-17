------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                           R E P O S I T O R Y                            --
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

--  $Id: repository.adb 6851 2009-07-22 12:37:17Z hugues $

with PolyORB_HI.Output;             use PolyORB_HI.Output;
with PolyORB_HI_Generated.Activity; use PolyORB_HI_Generated.Activity;

package body Repository is

   Message_1 : Message := 0;
   Message_2 : Message := 0;
   Message_3 : Message := 0;

   ----------
   -- Send --
   ----------

   procedure Send (Entity : Entity_Type) is
      Msg : Message;
   begin
      case Entity is
         when Node_A_Sender_1_K =>
            Message_1 := Message_1 + 1;
            Msg       := Message_1;

         when Node_A_Sender_2_K =>
            Message_2 := Message_2 + 1;
            Msg       := Message_2;

         when Node_A_Sender_3_K =>
            Message_3 := Message_3 + 1;
            Msg       := Message_3;

         when others =>
            Put_Line ("[Send] ERROR: Entity = " &  Entity_Image (Entity));
            raise Program_Error;
      end case;

      Put_Line ("[Send] "
                &  Entity_Image (Entity)
                & " sends"
                & Message'Image (Msg));
      Put_Value (Entity,
                 MultipleInstances_Sender_Interface'
                   (MultipleInstances_Sender_Port_Type'(Output), Msg));

   end Send;

   -------------
   -- Receive --
   -------------

   procedure Receive (Entity : Entity_Type; Input : Message) is
   begin
      Put_Line ("[Receive] "
                &  Entity_Image (Entity)
                & " receives"
                & Message'Image (Input));
   end Receive;

end Repository;
