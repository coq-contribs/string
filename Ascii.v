Require Import Bool.
Require Import ZArith.

(* Definition of ascii character as a 8 bits constructor *)
 
Inductive ascii : Set :=
    Ascii :
      bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> ascii.
 
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
 
Definition ascii_dec : forall a b : ascii, {a = b} + {a <> b}.
intros a b; case a; case b.
intros a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8.
case a1; case b1;
 (right; red in |- *; intros; discriminate) ||
   (case a2; case b2;
     (right; red in |- *; intros; discriminate) ||
       (case a3; case b3;
         (right; red in |- *; intros; discriminate) ||
           (case a4; case b4;
             (right; red in |- *; intros; discriminate) ||
               (case a5; case b5;
                 (right; red in |- *; intros; discriminate) ||
                   (case a6; case b6;
                     (right; red in |- *; intros; discriminate) ||
                       (case a7; case b7;
                         (right; red in |- *; intros; discriminate) ||
                           (case a8; case b8;
                             (right; red in |- *; intros; discriminate) ||
                               (case a8; case b8; auto)))))))).
Defined.

(* Example *)

Eval compute in (ascii_dec zero one).

 
(* Auxillary function that turns a positive into an ascii by
   looking at the last n bits, ie z mod 2^n *)

Fixpoint pos2ascii_aux (res acc : ascii) (z : positive) 
 (n : nat) {struct n} : ascii :=
  match n with
  | O => res
  | S n1 =>
      match z with
      | xH => app2 orb res acc
      | xI z' =>
          pos2ascii_aux (app2 orb res acc)
            (shift (fun x : bool => x) false acc) z' n1
      | xO z' =>
          pos2ascii_aux res (shift (fun x : bool => x) false acc) z' n1
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
           (2 * match a8 with
                | true => 1
                | false => 0
                end + match a7 with
                      | true => 1
                      | false => 0
                      end) + match a6 with
                             | true => 1
                             | false => 0
                             end) +
          match a5 with
          | true => 1
          | false => 0
          end) + match a4 with
                 | true => 1
                 | false => 0
                 end) + match a3 with
                        | true => 1
                        | false => 0
                        end) + match a2 with
                               | true => 1
                               | false => 0
                               end) +
      match a1 with
      | true => 1
      | false => 0
      end
  end.

(* Take too much time!  
(* Just to be sure we have not written non-sense: 256 cases! *)
Theorem ascii2nat2ascii:
  (a : ascii)  (nat2ascii (ascii2nat a)) = a.
Intros a; Case a.
Intros a1 a2 a3 a4 a5 a6 a7 a8; Case a1; Case a2; Case a3; Case a4; Case a5;
 Case a6; Case a7; Case a8; Simpl; Auto.
Qed.
*)