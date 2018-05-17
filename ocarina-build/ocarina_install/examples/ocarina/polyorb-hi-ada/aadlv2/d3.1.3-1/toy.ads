------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                                  T O Y                                   --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--    Copyright (C) 2006-2009 Telecom ParisTech, 2010-2015 ESA & ISAE.      --
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

--  $Id: toy.ads 6114 2009-02-05 13:22:05Z lasnier $

--  This package implements all the subprograms of the GNC/TMTC/POS
--  toy example AADL model.

with PolyORB_HI_Generated.Types; use PolyORB_HI_Generated.Types;

package Toy is

   procedure Read (Field : in out POS_Internal_Type);
   procedure Update (Field : in out POS_Internal_Type);

   procedure GNC_Job;
   procedure TMTC_Job;

   procedure GNC_Identity;
   procedure TMTC_Identity;
   --  At the first call, these subprogram print a welcome message. At
   --  the second call they print a "good bye" message.

end Toy;
