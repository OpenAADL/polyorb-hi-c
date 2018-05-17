------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                           R E P O S I T O R Y                            --
--                                                                          --
--                                 B o d y                                  --
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

with PolyORB_HI.Output; use PolyORB_HI.Output;

package body Repository is

   Cycle_Number  : Integer := 1;
   Message_Value : Simple_Type := 0;

   -----------------
   -- Init_Raiser --
   -----------------

   procedure Init_Raiser is
   begin
      Put_Line ("Raiser thread initialized");
   end Init_Raiser;

   -----------------
   -- Init_Worker --
   -----------------

   procedure Init_Worker is
   begin
      Put_Line ("Worker thread initialized");
   end Init_Worker;

   ------------
   -- Raiser --
   ------------

   procedure Raiser (M : out Simple_Type) is
   begin
      M := Message_Value;
      Message_Value := Message_Value + 1;
   end Raiser;

   --------------------
   -- Normal_Handler --
   --------------------

   procedure Normal_Handler (M : Simple_Type) is
   begin
      Put_Line ("NORMAL HANDLER received:" & Simple_Type'Image (M));
   end Normal_Handler;

   -----------------------
   -- Emergency_Handler --
   -----------------------

   procedure Emergency_Handler (M : Simple_Type) is
   begin
      Put_Line ("EMERGENCY HANDLER received:" & Simple_Type'Image (M));
   end Emergency_Handler;

   ------------------
   -- Lazy_Handler --
   ------------------

   procedure Lazy_Handler (M : Simple_Type) is
   begin
      Put_Line ("LAZY HANDLER received:" & Simple_Type'Image (M));
   end Lazy_Handler;

   -----------------------
   -- CE_Normal_Handler --
   -----------------------

   procedure CE_Normal_Handler
     (Entity : Entity_Type;
      P      : Worker_Impl_Port_Type) is
   begin
      if P = Message then
         Normal_Handler (Get_Value (Entity, P).Message_DATA);
      else
         Put_Line ("Received event: Work_Normally");
      end if;

      Next_Value (Entity, Worker_Impl_Port_Type'(P));
   end CE_Normal_Handler;

   --------------------------
   -- CE_Emergency_Handler --
   --------------------------

   procedure CE_Emergency_Handler
     (Entity : Entity_Type;
      P      : Worker_Impl_Port_Type) is
   begin
      if P = Message then
         Emergency_Handler (Get_Value (Entity, P).Message_DATA);
      else
         Put_Line ("Received event: Emergency_Occurred");
      end if;

      Next_Value (Entity, Worker_Impl_Port_Type'(P));
   end CE_Emergency_Handler;

   ---------------------
   -- CE_Lazy_Handler --
   ---------------------

   procedure CE_Lazy_Handler
     (Entity : Entity_Type;
      P      : Worker_Impl_Port_Type) is
   begin
      if P = Message then
         Lazy_Handler (Get_Value (Entity, P).Message_DATA);
      else
         Put_Line ("Received event: Everything_Is_Cool");
      end if;

      Next_Value (Entity, Worker_Impl_Port_Type'(P));
   end CE_Lazy_Handler;

   -----------
   -- Drive --
   -----------

   procedure Drive (Entity : Entity_Type) is
   begin
      if Cycle_Number mod 41 = 0 then
         Put_Line ("******** Emitting Work_Normally ********");
         Put_Value (Entity, Driver_Impl_Interface'(Port => Work_Normally));
      elsif Cycle_Number mod 201 = 0 then
         Put_Line ("******** Emitting Everything_Is_Cool ********");
         Put_Value (Entity,
                    Driver_Impl_Interface'(Port => Everything_Is_Cool));
      elsif Cycle_Number mod 400 = 0 then
         Put_Line ("******** Emitting Emergency_Occurred ********");
         Put_Value (Entity,
                    Driver_Impl_Interface'(Port => Emergency_Occurred));
      end if;

      Cycle_Number := Cycle_Number + 1;
   end Drive;

end Repository;
