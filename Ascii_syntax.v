Require Import Arith.
Require Export Ascii.

Declare ML Module "g_ascii_syntax".

(* 
  Ascii characters are parsed and pretty-print as follows:
 
    @"A"   represents the ascii character 65
    @""""  represents the ascii character 34
    @"\"  represents the ascii character 92
    @"032" represents the ascii character 32
*)


(* Parsing *)


(*
Grammar ascii explode :=.

Grammar constr constr0 :=
  ascii [ "@" ascii:explode($c)] -> [$c].
*)

Delimit Scope string_scope with string.
Open Scope string_scope.

(* Pretty-printing *)

(* <Warning> : Syntax is discontinued *)

(* Examples *)

Eval compute in zero.
Eval compute in (nat2ascii 65).
Eval compute in (fun x : bool => Ascii x x x x x x x x).
Eval compute in (Ascii false false false false false false false false).
Eval compute in (Ascii true false false false false false false false).
Eval compute in (Ascii false true false false false true false false).
Eval compute in (Ascii false false true true true false true false).
Eval compute in (Ascii true true true false true false false false).
