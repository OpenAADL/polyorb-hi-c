------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                  D E L A Y E D _ C O N N E C T I O N S                   --
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

--  $Id: delayed_connections.adb 6281 2009-03-27 13:46:45Z lasnier $

with PolyORB_HI.Output; use PolyORB_HI.Output;

package body Delayed_Connections is

   N_Sender_Cycles   : Simple_Type := 0;
   N_Receiver_Cycles : Simple_Type := 0;
   Msg               : Simple_Type := 0;

   ----------
   -- Send --
   ----------

   procedure Send
     (Data_Source : out Simple_Type;
      N_Cycle     : out Simple_Type)
   is
   begin
      N_Sender_Cycles := N_Sender_Cycles + 1;
      Msg             := Msg + 1;

      N_Cycle     := N_Sender_Cycles;
      Data_Source := Msg;

      Put_Line ("Sender: Cycle" & Simple_Type'Image (N_Cycle)
                & " sending" & Simple_Type'Image (Data_Source));
   end Send;

   -------------
   -- Receive --
   -------------

   procedure Receive
     (Data_Sink : Simple_Type;
      N_Cycle   : Simple_Type)
   is
   begin
      N_Receiver_Cycles := N_Receiver_Cycles + 1;

      Put_Line ("Receiver: Cycle" & Simple_Type'Image (N_Receiver_Cycles));
      Put_Line ("   received sender cycle:" & Simple_Type'Image (N_Cycle));
      Put_Line ("   received message     :" & Simple_Type'Image (Data_Sink));
   end Receive;

end Delayed_Connections;
