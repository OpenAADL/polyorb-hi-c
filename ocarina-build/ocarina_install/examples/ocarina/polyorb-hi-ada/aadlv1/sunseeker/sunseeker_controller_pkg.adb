------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--             S U N S E E K E R _ C O N T R O L L E R _ P K G              --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--    Copyright (C) 2007-2009 Telecom ParisTech, 2010-2018 ESA & ISAE.      --
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
with PolyORB_HI_Generated.Deployment;

package body Sunseeker_Controller_Pkg is

   use PolyORB_HI.Output;
   use PolyORB_HI_Generated.Deployment;

   Sunseekercontroller_Transfer : Single_Float := 0.0;
   ReferenceInput               : Single_Float := 0.0;

   Clock  : Single_Float := 0.0;
   Period : constant Single_Float := 0.01;
   --  ATTENTION: Period MUST be equal to the controller thread period
   --  (in seconds).

   -----------------------------------------
   -- Sunseekercontroller_Subprogram_Impl --
   -----------------------------------------

   procedure Sunseekercontroller_Subprogram_Impl
     (Controllerinput : out Single_Float;
      Outputfeedback  :     Single_Float)
   is
      Error               : Single_Float;
      Gain_Error_1        : Single_Float;
      Gain_Error          : Single_Float;
      Transfer_Fcn_Update : Single_Float;
   begin
      Put_Line (Node_Image (My_Node)
                & " CONSTROLLER INPUT:"
                & Single_Float'Image (Outputfeedback));

      if Clock < 1.0 then
         ReferenceInput := 0.0;
      else
         ReferenceInput := Clock - 1.0;
      end if;

      Error := ReferenceInput - Outputfeedback;

      Gain_Error_1 := Error * 0.1;
      Gain_Error := Gain_Error_1 * (-10_000.0);

      Transfer_Fcn_Update := Gain_Error
        - 170.0 * Sunseekercontroller_Transfer;

      Controllerinput := 29.17 * Sunseekercontroller_Transfer
        + Transfer_Fcn_Update;

      Sunseekercontroller_Transfer := Sunseekercontroller_Transfer
        + Period * Transfer_Fcn_Update;

      --  Mark a new cycle

      Clock := Clock + Period;

      Put_Line (Node_Image (My_Node)
                & " CONSTROLLER OUTPUT:"
                & Single_Float'Image (Controllerinput));
   end Sunseekercontroller_Subprogram_Impl;

end Sunseeker_Controller_Pkg;
