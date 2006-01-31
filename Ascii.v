Require Import Bool.
Require Import BoolEq.
Require Import ZArith.

(* Definition of ascii character as a 8 bits constructor *)
 
Inductive ascii : Set := Ascii (_ _ _ _ _ _ _ _ : bool) : ascii.

Delimit Scope my_char_scope with char.
Bind Scope my_char_scope with ascii.
 
Definition zero := Ascii false false false false false false false false.
 
Definition one := Ascii true false false false false false false false.
 
Definition app1 (f : bool -> bool) (a : ascii) :=
  match a with
  | Ascii a1 a2 a3 a4 a5 a6 a7 a8 =>
      Ascii (f a1) (f a2) (f a3) (f a4) (f a5) (f a6) (f a7) (f a8)
  end.
 
Definition app2 (f : bool -> bool -> bool) (a b : ascii) :=
  match a, b with
  | Ascii a1 a2 a3 a4 a5 a6 a7 a8, Ascii b1 b2 b3 b4 b5 b6 b7 b8 =>
      Ascii (f a1 b1) (f a2 b2) (f a3 b3) (f a4 b4) 
        (f a5 b5) (f a6 b6) (f a7 b7) (f a8 b8)
  end.
 
Definition shift (f : bool -> bool) (c : bool) (a : ascii) :=
  match a with
  | Ascii a1 a2 a3 a4 a5 a6 a7 a8 =>
      Ascii c (f a1) (f a2) (f a3) (f a4) (f a5) (f a6) (f a7)
  end.

(* Definition of a decidable function that is effective *)
 
Lemma bool_dec : forall a b : bool, {a = b} + { a <> b}.
 decide equality.
Defined.

Definition ascii_dec : forall a b : ascii, {a = b} + {a <> b}.
 decide equality; apply bool_dec.
Defined.

(* Example *)

Eval compute in (ascii_dec zero one).

Notation id := (fun x => x).

(* Auxillary function that turns a positive into an ascii by
   looking at the last n bits, ie z mod 2^n *)

Fixpoint pos2ascii_aux (res acc : ascii) (z : positive) 
 (n : nat) {struct n} : ascii :=
  match n with
  | O => res
  | S n1 =>
      match z with
      | xH => app2 orb res acc
      | xI z' => pos2ascii_aux (app2 orb res acc) (shift id false acc) z' n1
      | xO z' => pos2ascii_aux res (shift id false acc) z' n1
      end
  end.


(* Function that turns a positive into an ascii by
   looking at the last 8 bits, ie a mod 8 *)
 
Definition pos2ascii (a : positive) := pos2ascii_aux zero one a 8.
 
(* Function that turns a positive into an ascii by converting it to positive *)
Definition nat2ascii (a : nat) :=
  match a with
  | O => zero
  | S a' => pos2ascii (P_of_succ_nat a')
  end.
 
(* The opposite function *)
Definition ascii2nat (a : ascii) :=
  match a with
  | Ascii a1 a2 a3 a4 a5 a6 a7 a8 =>
      2 *
      (2 *
       (2 *
        (2 *
         (2 *
          (2 *
           (2 * (if a8 then 1 else 0)
            + (if a7 then 1 else 0))
           + (if a6 then 1 else 0))
          + (if a5 then 1 else 0))
         + (if a4 then 1 else 0))
        + (if a3 then 1 else 0))
       + (if a2 then 1 else 0))
      + (if a1 then 1 else 0)
  end.

(* Take (too) much time! *)
(* Just to be sure we have not written non-sense: 256 cases! *)
Theorem ascii2nat2ascii: forall a : ascii, nat2ascii (ascii2nat a) = a.
Proof.
  destruct a as [[|][|][|][|][|][|][|][|]]; compute; reflexivity.
Abort.
