Require Import Arith.
Require Export Ascii.
Require Export String.
Require Export Ascii_syntax.

Declare ML Module "g_string_syntax".

(* Parsing and pretty-printing of strings are the usual ones
*)

(* Parsing *)

(*
Grammar sstring explode :=.

Grammar constr constr0 :=
  sstring [ sstring:explode($c)] -> [$c].
*)

(* Pretty-printing *)

(* <Warning> : Syntax is discontinued *)
(* Examples *)

Eval compute in
  (String (nat2ascii 72)
     (String (nat2ascii 101)
        (String (nat2ascii 108)
           (String (nat2ascii 108) (String (nat2ascii 111) EmptyString))))).
Eval compute in EmptyString.
Eval compute in
  (fun x =>
   String x
     (String (Ascii false false false true false true true false)
        (String (Ascii true false true false false true true false)
           (String (Ascii false false true true false true true false)
              (String (Ascii false false true true false true true false)
                 (String (Ascii true true true true false true true false)
                    EmptyString)))))).
Eval compute in
  (String (Ascii false false true true true false true false) EmptyString).
Eval compute in
  (String (Ascii false true false false false true false false) EmptyString).
Eval compute in
  (let v :=
     String (Ascii false false false true false false true false)
       (String (Ascii true false true false false true true false)
          (String (Ascii false false true true false true true false)
             (String (Ascii false false true true false true true false)
                (String (Ascii true true true true false true true false)
                   (String
                      (Ascii false false false false false true false false)
                      (String
                         (Ascii true true true false true true true false)
                         (String
                            (Ascii true true true true false true true false)
                            (String
                               (Ascii false true false false true true true
                                  false)
                               (String
                                  (Ascii false false true true false true
                                     true false)
                                  (String
                                     (Ascii false false true false false true
                                        true false)
                                     (String
                                        (Ascii true false false false false
                                           true false false) EmptyString))))))))))) in
   substring 0
     (findex 0
        (String (Ascii false false false false false true false false)
           EmptyString) v) v).



