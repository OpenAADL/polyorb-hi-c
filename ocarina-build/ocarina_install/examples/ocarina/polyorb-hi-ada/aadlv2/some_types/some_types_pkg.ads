------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                       S O M E _ T Y P E S _ P K G                        --
--                                                                          --
--                                 S p e c                                  --
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

--  $Id: some_types_pkg.ads 6273 2009-03-25 17:36:51Z lasnier $

with PolyORB_HI_Generated.Types; use PolyORB_HI_Generated.Types;

package Some_Types_Pkg is

   procedure Emit_Boolean (Data_Source : out Boolean_Type);
   procedure Receive_Boolean (Data_Sink : in Boolean_Type);

   procedure Emit_Integer (Data_Source : out Integer_Type);
   procedure Receive_Integer (Data_Sink : in Integer_Type);

   procedure Emit_Array (Data_Source : out Array_Type_I);
   procedure Receive_Array (Data_Sink : in Array_Type_I);

   procedure Emit_String (Data_Source : out String_Type);
   procedure Receive_String (Data_Sink : in String_Type);

end Some_Types_Pkg;
