------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                    P O L Y O R B _ H I . O U T P U T                     --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--    Copyright (C) 2006-2009 Telecom ParisTech, 2010-2018 ESA & ISAE.      --
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

--  Debug facility of PolyORB HI

pragma SPARK_Mode (Off);

with PolyORB_HI.Streams;

package PolyORB_HI.Output is
   pragma Elaborate_Body;

   use PolyORB_HI.Streams;

   type Verbosity is
     (Verbose_L,
      --  Developer interest only, should never be displayed
      --  in a production environment.

      Normal_L,
      --  Informational message indicating progress of normal
      --  operation.

      Error_L
      --  Indication that an abnormal condition has been identified
      );

   Current_Mode : constant Verbosity := Normal_L;
   --  Curent debug level

   Verbose : constant Boolean := Current_Mode = Verbose_L;
   Normal : constant Boolean := Current_Mode <= Normal_L;
   Error : constant Boolean := Current_Mode <= Error_L;

   procedure Put_Line (Text : in String;
                       C1 : in String := "";
                       C2 : in String := "";
                       C3 : in String := ""
                      );
   --  As above but always displays the message

   procedure Put (Text : in String);
   --  As above but always displays the message

   procedure Dump (Stream : Stream_Element_Array;
                   Mode : Verbosity := Verbose_L);
   --  Dump the content of Stream in an hexadecimal format

private

   pragma Inline (Put_Line);

end PolyORB_HI.Output;
