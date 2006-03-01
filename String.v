Require Import Ascii.
(* option type *)
 
Inductive option (A : Set) : Set :=
  | Some : forall x : A, option A
  | None : option A.
 
Theorem SomeComp : forall (A : Set) (a b : A), a = b -> Some A a = Some A b.
intros A a b H'; rewrite H'; auto.
Qed.
Hint Resolve SomeComp.
(* Implementation of string as list of ascii characters *)
 
Inductive string : Set :=
  | EmptyString : string
  | String : ascii -> string -> string.
(* Equility is decidable *)
 
Definition string_dec : forall s1 s2 : string, {s1 = s2} + {s1 <> s2}.
 decide equality; apply ascii_dec.
Defined.
(* Usual append function for string *)
 
Fixpoint append (s1 : string) : string -> string :=
  fun s2 : string =>
  match s1 with
  | EmptyString => s2
  | String c s1' => String c (append s1' s2)
  end.
(* The number of character of a string *)
 
Fixpoint length (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => S (length s')
  end.
(* Return the nth character of a string *)
 
Fixpoint get (n : nat) (s : string) {struct s} : option ascii :=
  match s with
  | EmptyString => None _
  | String c s' => match n with
                   | O => Some _ c
                   | S n' => get n' s'
                   end
  end.
(* Two lists that are identical through get are syntactically equal *)
 
Theorem get_correct :
 forall s1 s2 : string, (forall n : nat, get n s1 = get n s2) <-> s1 = s2.
intros s1; elim s1; simpl in |- *.
intros s2; case s2; simpl in |- *; split; auto.
intros H; generalize (H 0); intros H1; inversion H1.
intros; discriminate.
intros a s1' Rec s2; case s2; simpl in |- *; split; auto.
intros H; generalize (H 0); intros H1; inversion H1.
intros; discriminate.
intros H; generalize (H 0); simpl in |- *; intros H1; inversion H1.
case (Rec s).
intros H0; rewrite H0; auto.
intros n; exact (H (S n)).
intros H; injection H; intros H1 H2 n; case n; auto.
rewrite H1; auto.
Qed.
(* The first elements  of (append s1 s2) are the ones of s1 *)
 
Theorem append_correct1 :
 forall (s1 s2 : string) (n : nat),
 n < length s1 -> get n s1 = get n (append s1 s2).
intros s1; elim s1; simpl in |- *; auto.
intros s2 n H; inversion H.
intros a s1' Rec s2 n; case n; simpl in |- *; auto.
intros n0 H; apply Rec; auto.
apply Lt.lt_S_n; auto.
Qed.
(* The last elements  of (append s1 s2) are the ones of s2 *)
 
Theorem append_correct2 :
 forall (s1 s2 : string) (n : nat),
 get n s2 = get (n + length s1) (append s1 s2).
intros s1; elim s1; simpl in |- *; auto.
intros s2 n; rewrite Plus.plus_comm; simpl in |- *; auto.
intros a s1' Rec s2 n; case n; simpl in |- *; auto.
generalize (Rec s2 0); simpl in |- *; auto.
intros n0; rewrite <- Plus.plus_Snm_nSm; auto.
Qed.
(* substring n m s returns the substring of s that starts
   at position n and of length m 
   if this does not make sense it returns "" *)
 
Fixpoint substring (n m : nat) (s : string) {struct s} : string :=
  match n with
  | O =>
      match m with
      | O => EmptyString
      | S m' =>
          match s with
          | EmptyString => s
          | String c s' => String c (substring 0 m' s')
          end
      end
  | S n' =>
      match s with
      | EmptyString => s
      | String c s' => substring n' m s'
      end
  end.
(* The substring is included in the initial string *)
 
Theorem substring_correct1 :
 forall (s : string) (n m p : nat),
 p < m -> get p (substring n m s) = get (p + n) s.
intros s; elim s; simpl in |- *; auto.
intros n; case n; simpl in |- *; auto.
intros m; case m; simpl in |- *; auto.
intros a s' Rec; intros n; case n; simpl in |- *; auto.
intros m; case m; simpl in |- *; auto.
intros p H; inversion H.
intros m' p; case p; simpl in |- *; auto.
intros n0 H; apply Rec; simpl in |- *; auto.
apply Lt.lt_S_n; auto.
intros n' m p H; rewrite <- Plus.plus_Snm_nSm; simpl in |- *; auto.
Qed.
(* The substring has at most m elements *)
 
Theorem substring_correct2 :
 forall (s : string) (n m p : nat),
 m <= p -> get p (substring n m s) = None _.
intros s; elim s; simpl in |- *; auto.
intros n; case n; simpl in |- *; auto.
intros m; case m; simpl in |- *; auto.
intros a s' Rec; intros n; case n; simpl in |- *; auto.
intros m; case m; simpl in |- *; auto.
intros m' p; case p; simpl in |- *; auto.
intros H; inversion H.
intros n0 H; apply Rec; simpl in |- *; auto.
apply Le.le_S_n; auto.
Qed.
(* Check if s1 is a prefix of s2 *)
 
Fixpoint prefix (s1 s2 : string) {struct s2} : bool :=
  match s1 with
  | EmptyString => true
  | String a s1' =>
      match s2 with
      | EmptyString => false
      | String b s2' =>
          match ascii_dec a b with
          | left _ => prefix s1' s2'
          | right _ => false
          end
      end
  end.
(* if s1 is a prefix of s2 we can get s1 by a substring at position O of s2 *)
 
Theorem prefix_correct :
 forall s1 s2 : string,
 prefix s1 s2 = true <-> substring 0 (length s1) s2 = s1.
intros s1; elim s1; simpl in |- *; auto.
intros s2; case s2; simpl in |- *; split; auto.
intros a s1' Rec s2; case s2; simpl in |- *; auto.
split; intros; discriminate.
intros b s2'; case (ascii_dec a b); simpl in |- *; auto.
intros e; case (Rec s2'); intros H1 H2; split; intros H3; auto.
rewrite e; rewrite H1; auto.
apply H2; injection H3; auto.
intros n; split; intros; try discriminate.
case n; injection H; auto.
Qed.
(* Check if starting at position n s1 occurs in s2, if
   so it returns the position *)
 
Fixpoint index (n : nat) (s1 s2 : string) {struct s2} : 
 option nat :=
  match s2 with
  | EmptyString =>
      match n with
      | O =>
          match s1 with
          | EmptyString => Some _ 0
          | String a s1' => None nat
          end
      | S n' => None nat
      end
  | String b s2' =>
      match n with
      | O =>
          match prefix s1 s2 with
          | true => Some _ 0
          | false =>
              match index 0 s1 s2' with
              | Some n => Some _ (S n)
              | None => None nat
              end
          end
      | S n' =>
          match index n' s1 s2' with
          | Some n => Some _ (S n)
          | None => None nat
          end
      end
  end.
(* Dirty trick to evaluate locally that prefix reduces itself *)
Opaque prefix.
(* If the result of index is (Some m), s1 in s2 at position m *)
 
Theorem index_correct1 :
 forall (n m : nat) (s1 s2 : string),
 index n s1 s2 = Some _ m -> substring m (length s1) s2 = s1.
intros n m s1 s2; generalize n m s1; clear n m s1; elim s2; simpl in |- *;
 auto.
intros n; case n; simpl in |- *; auto.
intros m s1; case s1; simpl in |- *; auto.
intros H; injection H; intros H1; rewrite <- H1; auto.
intros; discriminate.
intros; discriminate.
intros b s2' Rec n m s1.
case n; simpl in |- *; auto.
generalize (prefix_correct s1 (String b s2'));
 case (prefix s1 (String b s2')).
intros H0 H; injection H; intros H1; rewrite <- H1; auto.
case H0; simpl in |- *; auto.
case m; simpl in |- *; auto.
case (index 0 s1 s2'); intros; discriminate.
intros m'; generalize (Rec 0 m' s1); case (index 0 s1 s2'); auto.
intros x H H0 H1; apply H; injection H1; intros H2; injection H2; auto.
intros; discriminate.
intros n'; case m; simpl in |- *; auto.
case (index n' s1 s2'); intros; discriminate.
intros m'; generalize (Rec n' m' s1); case (index n' s1 s2'); auto.
intros x H H1; apply H; injection H1; intros H2; injection H2; auto.
intros; discriminate.
Qed.
(* If the result of index is (Some m), s1 does not occur in s2 before m *)
 
Theorem index_correct2 :
 forall (n m : nat) (s1 s2 : string),
 index n s1 s2 = Some _ m ->
 forall p : nat, n <= p -> p < m -> substring p (length s1) s2 <> s1.
intros n m s1 s2; generalize n m s1; clear n m s1; elim s2; simpl in |- *;
 auto.
intros n; case n; simpl in |- *; auto.
intros m s1; case s1; simpl in |- *; auto.
intros H; injection H; intros H1; rewrite <- H1.
intros p H0 H2; inversion H2.
intros; discriminate.
intros; discriminate.
intros b s2' Rec n m s1.
case n; simpl in |- *; auto.
generalize (prefix_correct s1 (String b s2'));
 case (prefix s1 (String b s2')).
intros H0 H; injection H; intros H1; rewrite <- H1; auto.
intros p H2 H3; inversion H3.
case m; simpl in |- *; auto.
case (index 0 s1 s2'); intros; discriminate.
intros m'; generalize (Rec 0 m' s1); case (index 0 s1 s2'); auto.
intros x H H0 H1 p; try case p; simpl in |- *; auto.
intros H2 H3; red in |- *; intros H4; case H0.
intros H5 H6; absurd (false = true); auto.
intros n0 H2 H3; apply H; auto.
injection H1; intros H4; injection H4; auto.
apply Le.le_O_n.
apply Lt.lt_S_n; auto.
intros; discriminate.
intros n'; case m; simpl in |- *; auto.
case (index n' s1 s2'); intros; discriminate.
intros m'; generalize (Rec n' m' s1); case (index n' s1 s2'); auto.
intros x H H0 p; case p; simpl in |- *; auto.
intros H1; inversion H1; auto.
intros n0 H1 H2; apply H; auto.
injection H0; intros H3; injection H3; auto.
apply Le.le_S_n; auto.
apply Lt.lt_S_n; auto.
intros; discriminate.
Qed.
(* If the result of index is None, s1 does not occur in s2 after n *)
 
Theorem index_correct3 :
 forall (n m : nat) (s1 s2 : string),
 index n s1 s2 = None _ ->
 s1 <> EmptyString -> n <= m -> substring m (length s1) s2 <> s1.
intros n m s1 s2; generalize n m s1; clear n m s1; elim s2; simpl in |- *;
 auto.
intros n; case n; simpl in |- *; auto.
intros m s1; case s1; simpl in |- *; auto.
case m; intros; red in |- *; intros; discriminate.
intros n' m; case m; auto.
intros s1; case s1; simpl in |- *; auto.
intros b s2' Rec n m s1.
case n; simpl in |- *; auto.
generalize (prefix_correct s1 (String b s2'));
 case (prefix s1 (String b s2')).
intros; discriminate.
case m; simpl in |- *; auto.
case s1; simpl in |- *; auto.
intros a s H H0 H1 H2; red in |- *; intros H3; case H.
intros H4 H5; absurd (false = true); auto.
case s1; simpl in |- *; auto.
intros a s n0 H H0 H1 H2;
 change (substring n0 (length (String a s)) s2' <> String a s) in |- *;
 apply (Rec 0); auto.
generalize H0; case (index 0 (String a s) s2'); simpl in |- *; auto; intros;
 discriminate.
apply Le.le_O_n.
intros n'; case m; simpl in |- *; auto.
intros H H0 H1; inversion H1.
intros n0 H H0 H1; apply (Rec n'); auto.
generalize H; case (index n' s1 s2'); simpl in |- *; auto; intros;
 discriminate.
apply Le.le_S_n; auto.
Qed.
(* Back to normal for prefix *)
Transparent prefix.
(* If we are searching for the Empty string and the answer is no
   this means that n is greater than the size of s *)
 
Theorem index_correct4 :
 forall (n : nat) (s : string),
 index n EmptyString s = None _ -> length s < n.
intros n s; generalize n; clear n; elim s; simpl in |- *; auto.
intros n; case n; simpl in |- *; auto.
intros; discriminate.
intros; apply Lt.lt_O_Sn.
intros a s' H n; case n; simpl in |- *; auto.
intros; discriminate.
intros n'; generalize (H n'); case (index n' EmptyString s'); simpl in |- *;
 auto.
intros; discriminate.
intros H0 H1; apply Lt.lt_n_S; auto.
Qed.
(* Same as index but with no optional type, we return O when it
   does not occur *)
 
Definition findex n s1 s2 :=
  match index n s1 s2 with
  | Some n => n
  | None => 0
  end.
