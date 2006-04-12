(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


Require Import Arith.
Require Export Ascii.

Declare ML Module "./g_local_ascii_syntax".

(* 
  Ascii characters are parsed and pretty-print as follows:
 
    "A" %char   represents the ascii character 65
    """"%char   represents the ascii character 34
    "\" %char   represents the ascii character 92
    32  %char   represents the ascii character 32
*)

(* Parsing *)

Open Scope local_char_scope.

(* Examples *)

Eval compute in zero.
Eval compute in (nat2ascii 65).
Eval compute in (fun x : bool => Ascii x x x x x x x x).
Eval compute in "000".
Eval compute in "001".
Eval compute in """".
Eval compute in "\".
Eval compute in "065".

