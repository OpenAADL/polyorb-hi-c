------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                                  M P C                                   --
--                                                                          --
--                                 S p e c                                  --
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

--  Implementation routines for the MPC Project Pilot model

with PolyORB_HI_Generated.Types; use PolyORB_HI_Generated.Types;

package MPC is

   procedure Update
     (Update_Value :        Record_Type_Impl;
      X            : in out Component_Type;
      Y            : in out Component_Type;
      Z            : in out Component_Type);

   procedure Read
     (Read_Value :    out Record_Type_Impl;
      X          : in out Component_Type;
      Y          : in out Component_Type;
      Z          : in out Component_Type);

   procedure Observe_Object (Data_Source : out Record_Type_Impl);

   procedure Watch_Object_Value (Read_Value : Record_Type_Impl);

end MPC;
