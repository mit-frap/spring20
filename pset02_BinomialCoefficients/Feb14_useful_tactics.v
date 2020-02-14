Require Import Coq.NArith.NArith. Open Scope N_scope.
Require Import Frap.Frap.
Require Import Pset2. Notation "x !" := (fact x) (at level 12, format "x !"). (* local in Pset2 *)
Set Default Goal Selector "!".

(* The tactic we introduce in each example is underlined like this. *)
                                             (********************)

Parameter whatever: Prop.

Goal forall (P Q R: Prop) (H1: P) (H2: Q) (IH: P -> Q -> R), R.
Proof.
  simplify.
  apply IH.
 (********)
Abort.

Goal forall (n m k: N), n = m.
Proof.
  simplify.
  Fail apply N.mul_cancel_r.
  apply N.mul_cancel_r with (p := n - k + 1).
 (****)               (****)
Abort.

Goal forall (n m k: N), n = m -> whatever.
Proof.
  simplify.
  apply N.mul_cancel_r with (p := n - k + 1) in H.
 (*****)              (****)                (**)
Abort.

Goal forall (n m k: N), n - k + 1 <> 0 -> n = m -> whatever.
Proof.
  simplify.
  eapply N.mul_cancel_r in H0.
 (******)              (**)
  2: {
    apply H.
  }
Abort.

Goal forall (P Q R S: Prop), (P -> S) -> (R -> S) -> P \/ Q \/ R -> S.
Proof.
  simplify.
  cases H1.
 (*****)
  - apply H. apply H1.
  - admit.
   (*****)
  - apply H0. apply H1.
Fail Qed.
Admitted.
(* Feel free to submit such incomplete proofs, they still get partial credit! *)

Goal forall (f : N -> N) (count : N)
            (IHcount : forall i start : N, i < count -> ith i (seq f count start) = f (start + i))
            (i start : N)
            (H : i < count + 1),
  ith i (f start :: seq f count (start + 1)) = f (start + i).
Proof.
  simplify.
  assert (i = 0 \/ 0 < i) as A. {
 (******)                (**)
    linear_arithmetic.
  }
  cases A.
  - subst. simplify. admit.
   (*****)  (* or "subst i" for just one var *)
  - assert (i = i - 1 + 1) as E by linear_arithmetic. rewrite E.
   (******)                    (**)
    unfold_recurse ith (i - 1).
Abort.

Goal forall (n x0 k: N),
    0 < k ->
    k + 1 < n ->
    n! = x0 * ((n - (k - 1))! * (k - 1)!) ->
    whatever.
Proof.
  intros n m.
 (******)
  intros.
 (******)
  replace (n - (k - 1)) with (n - k + 1) in H1 by linear_arithmetic.
 (*******)             (****)           (**)  (**)
  (* "in" and "by" are optional *)
  unfold_recurse fact (n - k).
Abort.

Goal forall (P Q R: Prop) (H0: Q) (x: N) (H: forall (a b: N), P -> Q -> a < b -> R), whatever.
Proof.
  simplify.
  specialize H with (b := x).
 (**********) (****)
  assert (3 < x) by admit.
  specialize H with (2 := H0) (3 := H1).
Abort.

Goal forall (f : N -> N) (start : N),
    f start = f (start + 0).
Proof.
  simplify.
  rewrite N.add_0_r.
 (*******)
  (* Options like "with (a := 2)", "in H", "by tactic" also work! *)
  equality.
Abort.

Goal forall (f : N -> N) (start : N),
    f start = f (start + 0).
Proof.
  simplify.
  f_equal.
 (*******)
  linear_arithmetic.
Abort.

Goal forall (f : N -> N) (start : N),
    f start = f (start + 0).
Proof.
  simplify.
  (* how many other ways can we find? *)
  assert (start + 0 = start) as E by linear_arithmetic.
  rewrite E.
Abort.

Goal forall (l: list N) (a b: N), ith 1 (a :: b :: l) = b.
Proof.
  intros.
  simplify.
 (********)
 (* unfold if it leads to a simpler term than the right-hand side of the definition *)
Abort.

Goal forall (P: Prop), P -> P.
Proof.
  simplify.
  assumption.
Abort.

Goal forall (n m: N), (n | n * m).
Proof.
  simplify.
  Locate "( _ | _ )".
  unfold N.divide.
 (******)
  exists m.
 (******)
  linear_arithmetic. (* Note: not actually linear *)
 (*****************)
Abort.

Goal forall (A B: Type) (f: A -> B) (a1 a2 a3: A),
    Some a1 = Some a2 ->
    Some a2 = Some a3 ->
    f a3 = f a1.
Proof.
  simplify.
  (* "Replace hypothesis H with other facts that can be deduced from the structure of H's statement".
     Looks at the structure of the arguments passed to the constructor of inductives appearing in H
     and deduces equalities from that, and then substitutes the equalities.
     Also particularly useful for Inductive Props, which we will see later. *)
  invert H.
 (******)
  invert H0.
  equality.
Abort.

Goal forall (A B: Type) (f: A -> B) (a1 a2 a3: A),
    Some a1 = Some a2 ->
    Some a2 = Some a3 ->
    f a3 = f a1.
Proof.
  simplify.
  equality.
 (********)
Abort.

Goal forall (a1 a2 b1 b2: N) (l1 l2: list N),
    a1 :: b1 :: l1 = a2 :: b2 :: l2 ->
    a1 = a2 /\ b1 = b2 /\ l1 = l2.
Proof.
  simplify.
  invert H.
 (******)
Abort.

Goal forall (P: Prop) (a b: N),
    (a < b -> ~P) ->
    P ->
    whatever.
Proof.
  simplify.
  assert (a < b \/ b <= a) as C by linear_arithmetic. cases C.
  - exfalso.
   (*******)
    unfold not in H.
    apply H.
    all: assumption.
Abort.

Goal forall (a : N) (l : list N),
    a :: l = [] ->
    whatever.
Proof.
  simplify.
  discriminate.
 (************)
Abort.

Goal forall (P Q R S T: Prop), (P \/ Q -> T) -> (R \/ S -> T) -> P \/ S -> T.
Proof.
  simplify.
  cases H1.
  - apply H. left. assumption.
  - apply H0. right. assumption.
Abort.

Goal forall (P Q R S T: Prop), (P \/ Q -> T) -> (R \/ S -> T) -> P \/ S -> T.
Proof.
  simplify.
  propositional.
 (*************)
Abort.

(* More tactics to discuss if we still have time:
   - constructor, econstructor
   - eassumption
   - eexists
   - firstorder
   - induct
   - left, right
   - maps_equal
   - trivial
   - transitivity
   - symmetry
*)

(* References:

   - FRAP book Appendix A.2. Tactic Reference (http://adam.chlipala.net/frap/frap_book.pdf)
   - Coq Reference Manual, Chapter on Tactics (https://coq.inria.fr/refman/proof-engine/tactics.html)
*)
