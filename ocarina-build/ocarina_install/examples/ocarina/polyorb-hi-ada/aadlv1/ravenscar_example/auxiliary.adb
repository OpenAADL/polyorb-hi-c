------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                            A U X I L I A R Y                             --
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

package body Auxiliary is

   Request_Counter : Range_Counter := 0;
   Run_Count       : Run_Counter   := 0;

   --------------------
   -- Due_Activation --
   --------------------

   function Due_Activation (Param : Range_Counter) return Boolean is
   begin
      Request_Counter := Request_Counter + 1;

      --  We make an activation due according to the caller's input
      --  parameter.

      return (Request_Counter = Param);
   end Due_Activation;

   ---------------
   -- Check_Due --
   ---------------

   function Check_Due return Boolean is
      Divisor : Natural;
   begin
      Run_Count := Run_Count + 1;
      Divisor   := Natural (Run_Count) / Factor;

      --  We force a check due according to an arbitrary criterion

      return ((Divisor * Factor) = Natural (Run_Count));
   end Check_Due;

end Auxiliary;
