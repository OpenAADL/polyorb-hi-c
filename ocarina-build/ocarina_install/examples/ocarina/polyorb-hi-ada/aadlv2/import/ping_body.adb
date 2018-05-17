------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                                 P I N G                                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--       Copyright (C) 2009 Telecom ParisTech, 2010-2018 ESA & ISAE.        --
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

--  $Id: ping_body.adb 6273 2009-03-25 17:36:51Z lasnier $

with PolyORB_HI.Output;

package body Ping is

   use PolyORB_HI.Output;

   Var : Array_Type_I := (0, 1, 2, 3);

   function Image (A : Array_Type_I) return String;
   function "+" (A : Array_Type_I; I : Simple_Type) return Array_Type_I;

   -----------
   -- Image --
   -----------

   function Image (A : Array_Type_I) return String is
   begin
      return "("
        & Simple_Type'Image (A (1))
        & ", " & Simple_Type'Image (A (2))
        & ", " & Simple_Type'Image (A (3))
        & ", " & Simple_Type'Image (A (4))
        & ")";
   end Image;

   ---------
   -- "+" --
   ---------

   function "+" (A : Array_Type_I; I : Simple_Type) return Array_Type_I is
   begin
      return (1 => A (1) + I,
              2 => A (2) + I,
              3 => A (3) + I,
              4 => A (4) + I);
   end "+";

   -----------------
   -- Do_Ping_Spg --
   -----------------

   procedure Do_Ping_Spg (Data_Source : out Array_Type_I) is
   begin
      Var := Var + 1;
      Data_Source := Var;
      Put_Line ("Sending PING" & Image (Var));
   end Do_Ping_Spg;

end Ping;
