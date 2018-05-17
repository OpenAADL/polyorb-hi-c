------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                                R A D A R                                 --
--                                                                          --
--                                 B o d y                                  --
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

with PolyORB_HI.Output;

package body Radar is

   use PolyORB_HI.Output;

   type Fake_Position_Index is mod 8;
   --  We use this index to retrieve fake position

   Fake_Positions : constant array (Fake_Position_Index'Range)
     of Target_Position_Impl :=
     ((1, 1), (2, 2), (3, 3), (1, 1), (2, 2), (3, 3), (2, 2), (3, 3));

   Fake_Index : Fake_Position_Index := 0;

   --------------
   -- Receiver --
   --------------

   procedure Receiver
     (Receiver_Out : out Target_Distance;
      Receiver_In : Target_Distance)
   is
      pragma Unreferenced (Receiver_In);
   begin
      Receiver_Out := Fake_Positions (Fake_Index).Rho;
      Put_Line ("Receiver, target is at distance" &
                  Target_Distance'Image (Receiver_Out));
      Fake_Index := Fake_Index + 1;
   end Receiver;

   ----------------
   -- Controller --
   ----------------

   procedure Controller
     (Controller_In : Motor_Position;
      Controller_Out : out Motor_Position)
   is
      pragma Unreferenced (Controller_In);
   begin
      Controller_Out := Fake_Positions (Fake_Index).Theta;
      Put_Line ("Controller, motor is at angular position "
                  & Motor_Position'Image (Controller_Out));
   end Controller;

   --------------
   -- Analyzer --
   --------------

   procedure Analyser
     (From_Receiver : Target_Distance;
      Analyser_Out : out Target_Position_Impl;
      From_Controller : Motor_Position) is
   begin
      Put_Line ("Analyser: target is at distance: "
                  & Target_Distance'Image (From_Receiver)
                  & " at angular position"
                  & Motor_Position'Image (From_Controller));
      Analyser_Out.Rho := From_Receiver;
      Analyser_Out.Theta := From_Controller;
   end Analyser;

   -----------------
   -- Transmitter --
   -----------------

   procedure Transmitter (Entity : Entity_Type) is
      pragma Unreferenced (Entity);
   begin
      Put_Line ("Transmitter");
   end Transmitter;

   -------------------
   -- Display_Panel --
   -------------------

   procedure Display_Panel (Display_In : Target_Position_Impl) is
   begin
      Put_Line ("Display_Panel: target is at ("
                  & Target_Distance'Image (Display_In.Rho) & ","
                  & Motor_Position'Image (Display_In.Theta) & ")");
   end Display_Panel;

end Radar;
