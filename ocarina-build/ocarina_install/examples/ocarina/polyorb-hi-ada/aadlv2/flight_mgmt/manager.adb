------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                              M A N A G E R                               --
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

--  $Id: manager.adb 6851 2009-07-22 12:37:17Z hugues $

with PolyORB_HI.Output;
with PolyORB_HI_Generated.Activity;

package body Manager is

   use PolyORB_HI.Output;
   use PolyORB_HI_Generated.Activity;

   Job : Ravenscar_Integer := 0;
   --  Cycle counter for Sensor_Sim

   ------------
   -- On_Req --
   ------------

   procedure On_Req (Entity : Entity_Type) is
   begin
      Put_Line ("==== Starting gear op ====");
      Put_Value (Entity,
                 Software_Landing_Gear_T_RS_Interface'(Port => Dummy_Out));
   end On_Req;

   -----------------
   -- On_Dummy_In --
   -----------------

   procedure On_Dummy_In (Entity : Entity_Type) is
   begin
      Put_Line ("==== Gear op done ====");
      Put_Value (Entity, Software_Landing_Gear_T_RS_Interface'(Port => Ack));
   end On_Dummy_In;

   ----------------------
   -- On_Stall_Warning --
   ----------------------

   procedure On_Stall_Warning
     (Entity        : Entity_Type;
      Stall_Warning : Ravenscar_Integer)
   is
   begin
      if Stall_Warning = 1 then
         Put_Line ("==== STALL ALARM"
                   & Ravenscar_Integer'Image (Stall_Warning)
                   & " from "
                   & Entity_Image
                       (Get_Sender
                        (Entity,
                         PolyORB_HI_Generated.Activity.Stall_Warning))
                   &" ====");
      else
         Put_Line ("==== False Alert"
                   & Ravenscar_Integer'Image (Stall_Warning)
                   & " from "
                   & Entity_Image
                       (Get_Sender
                        (Entity,
                         PolyORB_HI_Generated.Activity.Stall_Warning))
                   &" ====");
      end if;
   end On_Stall_Warning;

   -----------------------
   -- On_Engine_Failure --
   -----------------------

   procedure On_Engine_Failure (Entity : Entity_Type) is
      pragma Unreferenced (Entity);
   begin
      Put_Line ("==== ENGINE FAILURE ALARM ====");
   end On_Engine_Failure;

   -----------------
   -- On_Gear_Cmd --
   -----------------

   procedure On_Gear_Cmd (Entity : Entity_Type) is
   begin
      --  Raise the event port Gear_Req of the HCI thread

      Put_Value (Entity, Software_HCI_T_RS_Interface'(Port => Gear_Req));
   end On_Gear_Cmd;

   -----------------
   -- On_Gear_Ack --
   -----------------

   procedure On_Gear_Ack (Entity : Entity_Type) is
      pragma Unreferenced (Entity);
   begin
      Put_Line ("==== Gear Locked ====");
   end On_Gear_Ack;

   -----------------
   -- On_Operator --
   -----------------

   procedure On_Operator (Entity : Entity_Type) is
   begin
      Put_Value (Entity, Software_Operator_T_RS_Interface'(Port => Gear_Cmd));
   end On_Operator;

   -------------------
   -- On_Sensor_Sim --
   -------------------

   procedure On_Sensor_Sim (Entity : Entity_Type) is
      CR_V  : constant Ravenscar_Integer := 0;
      AoA_V : constant Ravenscar_Integer := 4;
   begin
      Job := Job + 1;

      if Job mod 40 = 0 then
         Put_Line ("==== Sensor_Sim setting soft stall ====");

         Put_Value (Entity, Software_Sensor_Sim_T_RS_Interface'(AoA, 41));
         Put_Value (Entity,
                    Software_Sensor_Sim_T_RS_Interface'(Climb_Rate, 4));
      elsif Job mod 201 = 0 then
         Put_Line ("==== Sensor_Sim setting hard stall ====");

         Put_Value (Entity, Software_Sensor_Sim_T_RS_Interface'(AoA, 25));
         Put_Value (Entity,
                    Software_Sensor_Sim_T_RS_Interface'(Climb_Rate, 9));
      elsif Job mod 401 = 0 then
         Put_Line ("==== Sensor_Sim raising engine failure ====");

         Put_Value (Entity,
                    Software_Sensor_Sim_T_RS_Interface'
                      (Port => Engine_Failure));
      else
         Put_Value (Entity, Software_Sensor_Sim_T_RS_Interface'(AoA, AoA_V));
         Put_Value (Entity,
                    Software_Sensor_Sim_T_RS_Interface'(Climb_Rate, CR_V));
      end if;
   end On_Sensor_Sim;

   ----------------------
   -- On_Stall_Monitor --
   ----------------------

   procedure On_Stall_Monitor (Entity : Entity_Type) is
      AoA_V : constant Ravenscar_Integer := Get_Value
        (Entity, Software_Stall_Monitor_T_RS_Port_Type'(AoA)).AoA_DATA;
      CR_V  : constant Ravenscar_Integer := Get_Value
        (Entity,
         Software_Stall_Monitor_T_RS_Port_Type'(Climb_Rate)).Climb_Rate_DATA;
   begin
      if AoA_V > 40 then
         Put_Value (Entity,
                    Software_Stall_Monitor_T_RS_Interface'(Stall_Warn, 2));
      elsif AoA_V > 22 and then CR_V < 10 then
         Put_Value (Entity,
                    Software_Stall_Monitor_T_RS_Interface'(Stall_Warn, 1));
      end if;
   end On_Stall_Monitor;

end Manager;
