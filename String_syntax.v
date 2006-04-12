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
Require Export String.
Require Export Ascii_syntax.

Declare ML Module "./g_local_string_syntax".

Open Scope local_string_scope.

(* Examples *)

Eval compute in "Hello".
Eval compute in "".
Eval compute in (fun x => String x "hello").
Eval compute in "\".
Eval compute in "A two-lines sentence that includes 
	a tabulation and a beep".
Eval compute in """".
Eval compute in (let v := "Hello world!" in substring 0 (findex 0 " " v) v).
