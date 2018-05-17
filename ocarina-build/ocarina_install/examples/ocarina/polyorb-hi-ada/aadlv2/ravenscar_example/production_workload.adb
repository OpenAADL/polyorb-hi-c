------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                  P R O D U C T I O N _ W O R K L O A D                   --
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

with Ada.Real_Time; use Ada.Real_Time;

package body Production_Workload is

   --  At elaboration time, this package evaluate the number of fixed
   --  point operation 1.0 / X to consume CPU during 1 millisecond.

   --  We use fixed point types to be compliant with restrictions for
   --  HIgh-Integrity systems (pragma Restriction No_Float).

   type Fixed_12_6 is delta 1.0E-6 digits 12;

   N_Base : constant Positive     := 1_000;
   F_Base : constant Fixed_12_6  := 1.0001;

   --  XMS or X Milli Seconds
   XMS    : constant Time_Span := Milliseconds (1);
   N_XMS  : Positive; --  Is computed at elaboration time

   --------------------------------
   -- Compute_During_N_Times_1ms --
   --------------------------------

   procedure Compute_During_N_Times_1ms (N : Positive) is
      X : Fixed_12_6 := F_Base;
   begin
      for I in 1 .. N_XMS * N loop
         X := 1.0 / X;
      end loop;
   end Compute_During_N_Times_1ms;

begin
   declare
      B : Time;
      --  Begin of the measure

      E : Time;
      --  End od the measure

      X : Fixed_12_6 := F_Base;
   begin

      --  Measure N_Base times the same operation 1/X

      B := Clock;
      for I in 1 .. N_Base loop
         X := 1.0 / X;
      end loop;
      E := Clock;

      --  Calculate the number of operation necessary to consume CPU
      --  during 1 sec.

      N_XMS := Positive ((XMS * N_Base) / (E - B));

      --  Redo the measure to obtain a more precise N_XMS value

      B := Clock;
      for I in 1 .. N_XMS loop
         X := 1.0 / X;
      end loop;
      E := Clock;
      N_XMS := Positive ((XMS * N_XMS) / (E - B));
   end;
end Production_Workload;
