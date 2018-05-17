------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                               P R I M E S                                --
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

with PolyORB_HI.Output;             use PolyORB_HI.Output;
with PolyORB_HI_Generated.Activity; use PolyORB_HI_Generated.Activity;

package body Primes is

   Finder_Cycle   : Integer_Type := 0;
   N_Primes_One   : Integer_Type := 0;
   N_Primes_Two   : Integer_Type := 0;
   N_Primes_Three : Integer_Type := 0;

   function Is_Prime (N : Integer_Type) return Boolean;

   --------------------
   -- Raise_If_Prime --
   --------------------

   procedure Raise_If_Prime (Entity : Entity_Type) is
   begin
      if Is_Prime (Finder_Cycle) then
         Put_Value (Entity,
                    Prime_Finder_Impl_Interface'(Found_Prime, Finder_Cycle));
      end if;

      Finder_Cycle := Finder_Cycle + 1;
   end Raise_If_Prime;

   ---------------------------
   -- On_Received_Prime_One --
   ---------------------------

   procedure On_Received_Prime_One
     (Entity         : Entity_Type;
      Received_Prime : Integer_Type)
   is
      pragma Unreferenced (Entity);
   begin
      N_Primes_One := N_Primes_One + 1;

      Put_Line ("Reporter ONE: received new prime:"
                & Integer_Type'Image (Received_Prime));
   end On_Received_Prime_One;

   ---------------------------
   -- On_Received_Prime_Two --
   ---------------------------

   procedure On_Received_Prime_Two
     (Entity         : Entity_Type;
      Received_Prime : Integer_Type)
   is
      pragma Unreferenced (Entity);
   begin
      N_Primes_Two := N_Primes_Two + 1;

      Put_Line ("Reporter TWO: received new prime:"
                & Integer_Type'Image (Received_Prime));
   end On_Received_Prime_Two;

   -----------------------------
   -- On_Received_Prime_Three --
   -----------------------------

   procedure On_Received_Prime_Three
     (Entity         : Entity_Type;
      Received_Prime : Integer_Type)
   is
      pragma Unreferenced (Entity);
   begin
      N_Primes_Three := N_Primes_Three + 1;

      Put_Line ("Reporter THREE: received new prime:"
                & Integer_Type'Image (Received_Prime));
   end On_Received_Prime_Three;

   ----------------
   -- Report_One --
   ----------------

   procedure Report_One (Entity : Entity_Type) is
      pragma Unreferenced (Entity);
   begin
      Put_Line ("*** Reporter ONE periodic report, total primes:"
                & Integer_Type'Image (N_Primes_One)
                & " ***");
   end Report_One;

   ----------------
   -- Report_Two --
   ----------------

   procedure Report_Two (Entity : Entity_Type) is
      pragma Unreferenced (Entity);
   begin
      Put_Line ("*** Reporter TWO periodic report, total primes:"
                & Integer_Type'Image (N_Primes_Two)
                & " ***");
   end Report_Two;

   ------------------
   -- Report_Three --
   ------------------

   procedure Report_Three (Entity : Entity_Type) is
      pragma Unreferenced (Entity);
   begin
      Put_Line ("*** Reporter THREE periodic report, total primes:"
                & Integer_Type'Image (N_Primes_Three)
                & " ***");
   end Report_Three;

   --------------
   -- Is_Prime --
   --------------

   function Is_Prime (N : Integer_Type) return Boolean is
      P : Boolean := True;
   begin
      if N < 2 then
         return False;
      elsif N = 2 then
         return True;
      else
         for D in 2 .. N / 2 + 1 loop
            P := N mod D /= 0 and then P;
            exit when not P;
         end loop;

         return P;
      end if;
   end Is_Prime;

end Primes;
