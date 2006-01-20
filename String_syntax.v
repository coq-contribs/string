Require Import Arith.
Require Export Ascii.
Require Export String.
Require Export Ascii_syntax.

Declare ML Module "g_string_syntax".

Open Scope string_scope.

(* Examples *)

Eval compute in "Hello".
Eval compute in "".
Eval compute in (fun x => String x "hello").
Eval compute in "\".
Eval compute in "A two-lines sentence that includes 
	a tabulation and a beep".
Eval compute in """".
Eval compute in (let v := "Hello world!" in substring 0 (findex 0 " " v) v).
