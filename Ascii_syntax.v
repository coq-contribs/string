Require Import Arith.
Require Export Ascii.

Declare ML Module "g_ascii_syntax".

(* 
  Ascii characters are parsed and pretty-print as follows:
 
    "A" %char   represents the ascii character 65
    """"%char   represents the ascii character 34
    "\" %char   represents the ascii character 92
    32  %char   represents the ascii character 32
*)

(* Parsing *)

Open Scope char_scope.

(* Examples *)

Eval compute in zero.
Eval compute in (nat2ascii 65).
Eval compute in (fun x : bool => Ascii x x x x x x x x).
Eval compute in "000".
Eval compute in "001".
Eval compute in """".
Eval compute in "\".
Eval compute in "065".

