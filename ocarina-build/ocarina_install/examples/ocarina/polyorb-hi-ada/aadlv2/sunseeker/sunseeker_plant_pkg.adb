------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                  S U N S E E K E R _ P L A N T _ P K G                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--    Copyright (C) 2008-2009 Telecom ParisTech, 2010-2018 ESA & ISAE.      --
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

--  $Id: sunseeker_plant_pkg.adb 6879 2009-07-25 11:36:09Z lanarre $

with PolyORB_HI.Output;
with PolyORB_HI_Generated.Deployment;

package body Sunseeker_Plant_Pkg is

   use PolyORB_HI.Output;
   use PolyORB_HI_Generated.Deployment;

   Sunseekerplant_Integrator   : Single_Float := 0.0;
   Sunseekerplant_Transfer_Fcn : Single_Float := 0.0;

   Period : constant Single_Float := 0.01;
   --  ATTENTION: Period MUST be equal to the controller thread period
   --  (in seconds).

   --------------------------------------
   -- Sunseekerplant_Subprogram_Beacon --
   --------------------------------------

   procedure Sunseekerplant_Subprogram_Beacon
     (Controllerinput :     Single_Float;
      Outputfeedback  : out Single_Float)
   is
      Feedback_Error : Single_Float;
      Feedback : Single_Float;
      Integrator_Output : Single_Float;
      Plant_Output : Single_Float;
      Preamp_Output : Single_Float;
      Transfer_Fcn_update : Single_Float;

   begin
      Put_Line (Node_Image (My_Node)
                & " PLANT INPUT:"
                & Single_Float'Image (Controllerinput));

      Preamp_Output := Controllerinput * (-2.0);

      Integrator_Output := Sunseekerplant_Integrator;

      Plant_Output := 0.002 * Sunseekerplant_Transfer_Fcn;

      Feedback := Plant_Output * 0.012_5;

      Outputfeedback := Integrator_Output * 0.001_25;

      Sunseekerplant_Integrator := Sunseekerplant_Integrator
        + 0.001 * Plant_Output;

      Feedback_Error := Preamp_Output - Feedback;

      Transfer_Fcn_Update := 1.0E+6 * Feedback_Error;

      sunseekerplant_Transfer_Fcn := Sunseekerplant_Transfer_Fcn
        + Period * Transfer_Fcn_Update;

      Put_Line (Node_Image (My_Node)
                  & " PLANT OUTPUT:"
                  & Single_Float'Image (Outputfeedback)
                  & " ERROR:"
                  & Single_Float'Image (Feedback_Error));
   end Sunseekerplant_Subprogram_Beacon;

end Sunseeker_Plant_Pkg;
