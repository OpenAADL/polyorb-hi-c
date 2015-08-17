------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                        H E A D E R S _ P O _ H I                         --
--                                                                          --
--                                 B o d y                                  --
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

with Ada.Calendar;            use Ada.Calendar;
with Ada.Characters.Handling; use Ada.Characters.Handling;
with Ada.Command_Line;
with Ada.Directories;         use Ada.Directories;
with Ada.Exceptions;
with Ada.Strings.Unbounded;   use Ada.Strings.Unbounded;
with Ada.Text_IO;             use Ada.Text_IO;
with Ada.Unchecked_Deallocation;

with GNAT.Regpat; use GNAT.Regpat;

procedure Headers_PO_HI is

   subtype Line_Type is String (1 .. 256);

   type Kind_Type is (None, Unit_Spec, Unit_Body, Project_File);

   Add_Header : Boolean := True;

   Header_Template : constant String :=
     "/*" & ASCII.LF &
     " * This is a part of PolyORB-HI-C distribution, a minimal" & ASCII.LF &
     " * middleware written for generated code from AADL models." & ASCII.LF &
     " * You should use it with the Ocarina toolsuite." & ASCII.LF &
     " *" & ASCII.LF &
     " * For more informations, please visit http://taste.tuxfamily.org/wiki"
     & ASCII.LF & " *" & ASCII.LF & "@COPYRIGHT@" & " */" & ASCII.LF;

   -------------------------
   -- Utility subprograms --
   -------------------------

   function Copyright_Line (First_Year, Last_Year : Year_Number) return String;
   --  Return copyright notice for the specified year range

   function Doublespace (S : String) return String;
   --  Return S with double spacing inserted if short enough to fit the header
   --  comment box; otherwise return S unchanged.

   function Has_Prefix (Prefix : String; S : String) return Boolean;
   --  True iff S starts with Prefix

   function Image (Year : Year_Number) return String;
   --  Return the string image of Year (with no leading space)

   procedure Update_Header (Filename : String);
   --  Output the contents of Filename with updated header

   --------------------
   -- Copyright_Line --
   --------------------

   function Copyright_Line
     (First_Year, Last_Year : Year_Number) return String
   is
      Range_Image : constant String :=
        Image (First_Year) & "-" & Image (Last_Year);
      Last : Positive := Range_Image'Last;
   begin
      if First_Year = Last_Year then
         Last := Range_Image'First + 3;
      end if;
      if First_Year < 2009 then
         return "Copyright (C) " &
           Image (First_Year) & "-2009 Telecom ParisTech, "
           & "2010-" & Image (last_year) & " ESA & ISAE.";
      elsif First_Year = 2009 then
         return "Copyright (C) " &
           Image (First_Year) & " Telecom ParisTech, "
           & "2010-" & Image (last_year) & " ESA & ISAE.";

      else
         return "Copyright (C) " & Range_Image (Range_Image'First .. Last)
           & " ESA & ISAE.";
      end if;
   end Copyright_Line;

   -----------------
   -- Doublespace --
   -----------------

   function Doublespace (S : String) return String is
   begin
      if S'Length > 35 then
         return S;
      else
         declare
            Res : String (2 * S'First .. 2 * S'Last) := (others => ' ');
         begin
            for J in S'Range loop
               Res (2 * J) := S (J);
            end loop;
            return Res;
         end;
      end if;
   end Doublespace;

   ----------------
   -- Has_Prefix --
   ----------------

   function Has_Prefix (Prefix : String; S : String) return Boolean is
   begin
      return S'Length >= Prefix'Length
        and then S (S'First .. S'First + Prefix'Length - 1) = Prefix;
   end Has_Prefix;

   -----------
   -- Image --
   -----------

   function Image (Year : Year_Number) return String is
      Res : constant String := Year'Img;
   begin
      return Res (Res'First + 1 .. Res'Last);
   end Image;

   -------------------
   -- Update_Header --
   -------------------

   procedure Update_Header (Filename : String) is

      Ofilename : constant String := Filename & ".UHN";

      ----------------------
      -- Global variables --
      ----------------------

      UName : Unbounded_String;
      UKind : Kind_Type := None;

      Last_Copyright_Year  : Year_Number := Year (Clock);
      First_Copyright_Year : Year_Number := Last_Copyright_Year;

      type Substs is (Copyright);
      type String_Access is access all String;

      procedure Free is new Ada.Unchecked_Deallocation (String, String_Access);

      procedure Output_Header (Outf : File_Type);
      --  Output header templates with appropriate substitutions

      procedure Output_Header (Outf : File_Type) is
         Pattern : Unbounded_String;

         function "+" (S : String) return Unbounded_String is
         begin
            return To_Unbounded_String (" * " & S & ASCII.LF);
         end "+";

         Subst_Strings : array (Substs) of Unbounded_String :=
           (Copyright        =>
              +Copyright_Line (First_Copyright_Year, Last_Copyright_Year));

      begin
         Pattern := To_Unbounded_String ("@(");
         for J in Substs loop
            Append (Pattern, J'Img);
            if J /= Substs'Last then
               Append (Pattern, '|');
            end if;
         end loop;
         Append (Pattern, ")@");

         declare
            Matcher : constant Pattern_Matcher :=
                        Compile (To_String (Pattern), Single_Line);
            Matches : Match_Array (0 .. Paren_Count (Matcher));
            Start   : Positive := Header_Template'First;
         begin
            while Start <= Header_Template'Last loop
               Match (Matcher,
                      Header_Template (Start .. Header_Template'Last), Matches);

               if Matches (0) = No_Match then
                  Put (Outf, Header_Template (Start .. Header_Template'Last));
                  exit;
               end if;
               declare
                  Loc_Token  : Match_Location renames Matches (1);
               begin
                  Put (Outf, Header_Template (Start .. Loc_Token.First - 2));
                  Put (Outf,
                    To_String (Subst_Strings
                      (Substs'Value (Header_Template (Loc_Token.First
                                                   .. Loc_Token.Last)))));
                  Start := Loc_Token.Last + 2;
               end;

            end loop;
         end;
      end Output_Header;

      Line : Line_Type;
      Last : Natural;

      Copyright_Matcher : constant Pattern_Matcher :=
        Compile ("Copyright \([cC]\) ([0-9]+)");
      Copyright_Matches : Match_Array (0 .. Paren_Count (Copyright_Matcher));

      F    : File_Type;
      Outf : File_Type;

      In_Header : Boolean := True;
      Got_Copyright : Boolean := False;
      Buf : Unbounded_String;

      Basename : constant String := Base_Name (Filename);
   begin
      Open   (F, In_File, Filename);
      Create (Outf, Out_File, Ofilename);

      begin
         loop
            Get_Line (F, Line, Last);
            if Last = Line'Last then
               raise Constraint_Error with "line too long";
            end if;
            if Last < 2
              or else (Line (1 .. 2) /= "/*"
                         and then Line (1 ..2) /= " *"
                         and then Line (1 ..2) /= "*/")
            then
               In_Header := False;
               exit;
            end if;

            if In_Header then
               Match (Copyright_Matcher, Line (1 .. Last), Copyright_Matches);
               if (not Got_Copyright)
                 and then Copyright_Matches (0) /= No_Match
               then
                  First_Copyright_Year :=
                    Year_Number'Value (Line (Copyright_Matches (1).First
                                          .. Copyright_Matches (1).Last));
                  Got_Copyright := True;
               end if;
            end if;
         end loop;

         if not Got_Copyright then
            Reset (F);
         end if;

         if Add_Header then
            Output_Header (Outf);
            Put_Line (To_String (Buf));
            New_Line (Outf);
         end if;

         Put (Outf, To_String (Buf));

         while not End_Of_File (F) loop
            Get_Line (F, Line, Last);
            if Last = Line'Last then
               raise Constraint_Error with "line too long";
            end if;
            Put_Line (Outf, Line (1 .. Last));
         end loop;

         Close (F);
         Close (Outf);
         Delete_File (Filename);
         Rename (Ofilename, Filename);
      exception
         when E : others =>
            Put_Line (Standard_Error, "Update of " & Filename & " failed:");
            Put_Line (Ada.Exceptions.Exception_Information (E));
            Delete_File (Ofilename);
      end;

   end Update_Header;

   --  Start of processing for Headers_PO_HI

begin
   if Ada.Command_Line.Argument_Count = 2 then
      if Ada.Command_Line.Argument (1) = "-noh" then
         Add_Header := False;
      end if;
      Put_Line ("Removing header from " &  Ada.Command_Line.Argument (2));
      Update_Header (Ada.Command_Line.Argument (2));
   else

      Put_Line ("Adding header to " &  Ada.Command_Line.Argument (1));
      Update_Header (Ada.Command_Line.Argument (1));
   end if;
end Headers_PO_HI;
