Require Import Frap ZArith. Local Open Scope Z_scope.
Arguments Z.add !_ !_.

(* A developed library includes multiple equivalent definitions
   for the same concept *along with the proofs of equivalence*.
   However, it is the user's responsibility to work with the
   definition appropriate for their argument. For this part, the
   goal is to prove that for any x, the least significant bit of
   x+x+x+x is low. *)

Lemma bad_idea (x : Z) : Z.testbit (x+x+x+x) 0 = false.
Proof.
  Search Z.testbit Z.add.
  (* nothing obviously useful... *)
  (* what if we tried a direct proof? *)
  unfold Z.add; unfold Z.testbit.
  (* the sheer size of the definitions makes this seem daunting... *)
Abort.

(* more broadly, because the [Z] library uses binary arithmetic
   (and another layer of indirection, the [positive] library),
   it is often quite unwieldy to reason using the definitions of
   the functions (in terms of bit operations). Instead, it is
   usually more practical to do the proofs using the extensive
   collection of lemmas provided in the standard library, even
   if that also requires a slight detour. *)

Lemma using_modular_arithmetic (x : Z) : Z.testbit (x+x+x+x) 0 = false.
Proof.
  Search Z.testbit Z.modulo.
  rewrite Z.bit0_eqb.
  SearchAbout (_*?m mod ?m).
  Check Z.mod_mul x 2. (* not quite...*)
  Check Z.mod_mul (x*2) 2.

  assert (helper : x + x + x + x = x*2*2).
  { linear_arithmetic. }
  rewrite helper.
  rewrite Z.mod_mul.
  2: {
    linear_arithmetic.
  }

  equality.
Qed.

(* Proof design needs to consider both the idea of the proof, as
   informal or vague as it is, and the proof steps made possible
   by the lemmas and primitive proof rules of the system.
   The first attempt at proving that x+x+x+x has least significant
   bit false was wholly unguided: there was no plan about how the
   proof would go, and no list of lemmas to be used in individual
   steps. The second attempt was based on the author's past
   experience that the modular arithmetic library is decent, thus
   seeking a proof strategy that would relate [Z.testbit] and [+]
   to modular arithmetic. *)

(* But what if the world just began today? [Z.testbit], [+] and
   [mod] are standard-library functions operating on the
   standard-library-defined data structure [Z], and we were able
   to complete the last proof using the lemmas provided about
   them. this is not goint to be the case for (a) any function or
   data structure you define yourself and (b) most objects of
   study in this class. In particular, most programs are best
   represented as abstract syntax trees, using a data structure
   specific to the programming language in question. And while a new
   function is often made up of existing functions and can be reasoned
   about using lemmas about those, a freshly-defined data structure is
   only subject to the primitive proof rules of the proof assistant. *)

 (* So what can one prove about a new data structure in Coq?
   
    The key starting point is the *induction lemma* generated
    when the datatype is declared. In some proof assistants, 
    generalized induction/recursion lemmas are the primitive
    interface to datatypes and pattern-matching is defined in
    terms of that. In Coq pattern-matching is primitive instead,
    but induction lemmas are equally powerful, and since they are
    lemmas, they can be displayed using Check. The induction lemma
    for a datatype says precisely what you need to do to prove
    forall-quantified statements about that datatype.
    (as long as the induction-lemma generation is working
    correctly, that is...) *)

(* First let's consider a simple case where universally-quantified
  statements are best proven by considering a finite number of cases
  one-by-one. This degenerate case nonetheless illustrates the key
  mechanics for proving stuff about new datatypes in Coq. *)
Inductive bool :=
| true
| false.
Check bool.
Check true.
Check false.
Check bool_ind. (* read this one very carefully *)

Definition bool2Z (b : bool) : Z :=
  match b with
  | true => 1
  | false => 0
  end.

Lemma bool2Z_lt_2 : forall b, 0 <= bool2Z b < 2.
Proof.
  apply bool_ind.

  (* pause here *)

  (* interlude: let's inspect P inferred by [apply] *)
  Show Proof.
  (* The "fun parameter : type_of_parameter => result" is an anonymous function (lambda). *)
  (* They work the same way as named functions such as [bool2Z] or [tablemul]. *)
  (* In fact, named functions are just named references to anonymous functions: *)
  Print bool2Z.


  { unfold bool2Z.
    linear_arithmetic. }
  { unfold bool2Z.
    linear_arithmetic. }
Qed.


(* notice the lemma statement was written suggestively to have
a "forall" in the goal (as opposed to a variable in the givens)
  when [apply] was called. This is to help [apply] infer [P].
  Let's see what can happen if we don't do that. *)


Definition andb (a : bool) (b : bool) :=
 match a, b with
 | true, true => true
 | _ , _ => false
 end. 

Lemma andb_false_r (b : bool) : andb b false = false.
Proof.
  apply bool_ind. (* <-- not what you want *)
  Show Proof.
  (* We see that [apply] inferred [P := eq (andb b false)] *)
  (* An use of an induction lemma should prove [forall x, P x] *)
  (* Here [forall x, P x] would be
     [forall x, eq (andb b false) x] which is notation for
     [forall x, andb b false = x] which we know is the same as
     [forall x,        false = x] *)
  (* This is not true, so the two remaining cases of this proof
     must be impossible *)
Abort.

Definition andb_false_P (b : bool) := 0 = 1 (* CHANGE THIS *).

Reset andb_false_P.
Definition andb_false_P (b : bool) := andb b false = false.

Check bool_ind andb_false_P.
(* fancier code for better view (you don't need to understand this): *)
Eval cbv [andb_false_P] in ltac:(let t := type of (bool_ind andb_false_P) in exact t).
(* the preconditions should look provable, and the conclusion
* should be the lemma you want to prove *)

Lemma andb_false_r (b : bool) : andb b false = false.
Proof.
  apply (bool_ind andb_false_P).
  { unfold andb_false_P.
    unfold andb.
    equality. }
  { unfold andb_false_P.
    unfold andb.
    equality. }
Qed.

(* Fortunately, [apply] is not actually the state of art in
   inferring induction predicates -- there is a more ergonomic
   alternative. However, make no mistake, what is about to
   described will save *keystrokes*, not *braincycles* --
   the mechanics of induction-lemma-based proof still apply,
   and careful thought is as necessary always. *) 
(* The [induct] command is a shorthand that constructs the
   inductive statement [P] by treating the current goal as a
   function of the specified argument, here [b]. It is a rather
   thing wrapper, operating by the garbage-in-garbage-out
   principle. Picking the inductive statement is *the* *most*
   *important* *thing* about induction proofs, and reading an
   already-completed proof makes that "just calls [induct]"
   makes it look deceptively easy. We recommend putting more
   thought into inductive-statement-selection than initially seems
   reasonable, especially if the inductive statement itself is an
   implication. In fact, entire disciplines of program-reasoning
   tools such as type systems and program logics can be seen as
   "just" inductive statements that hold througout the execution
   of the program. *)

Lemma andb_false_r' (b : bool) : andb b false = false.
Proof.
  induct b.
  Show Proof. (* note the inferred argument to [bool_ind] *)
              (* compare it to the one in the [Abort]ed attempt,
                 and the more manual [apply]-based oned *)
  { unfold andb.
    equality. }
  { unfold andb.
    equality. }
Qed.

(* Okay, enough of playing with "induction" on finite types, let's do
 * something more real. Just to get it over with, here are the
   induction lemmas for natural numbers and integers. Read them,
   and match your existing understanding of induction (on numbers)
   to them: identify the base case, the inductive case, and the
   conclusion. *)
Check nat_ind. (* [nat] is natural numbers, [S x] is [x+1] *)
Check N.peano_ind. (* [N] is another encoding of natural numbers *)
Check Z.peano_ind. (* [Z] is an encoding of integers *)
(* It just so happens that the [nat] induction lemma above is
 * auto-generated and the ones for [N] and [Z] are proven by hand, but
   as a mere user of these datatypes (accessing them using existing
   functions, not their structure) you really don't need to care. *)

Inductive list :=
| cons (head : Z) (tail : list)
| nil.
Check list_ind. (* read this one very carefully *)

Fixpoint length (l : list) : Z :=
  match l with
  | nil => 0
  | cons _ ll => 1 + length ll
  end.

(* state and prove that lenghtZ returns non-negative numbers by
   explicitly writing down [P] and applying [list_ind P] *)


Lemma length_nonnegative : forall (l : list), 0 <= length l.
Proof.
  apply (list_ind (fun l => 0 <= length l)).
  { unfold length in *.
    linear_arithmetic. }
  { unfold length.
    linear_arithmetic. }
Qed.

Lemma length_nonnegative' : forall (l : list), 0 <= length l.
Proof.
  induct l; unfold length in *; linear_arithmetic.
Qed.





(* NB: [induct] is not magic. It applies a rather dumb syntactic
 * heuristic to infer [P]. The choice of [P] is obvious if either
   - the goal is [forall x y], ... and [induct x] is called
   In particular, COUNTER-INTUITIVE behavior can occur when
   - the goal is [forall x y], ... and [induct y] is called
   - [x] is a variable in the context and [induct x] is called
     while [y] is also in the context
   In these cases, the [P] will refer to a fixed [y], whereas it
   may be desirable to have [P := forall y, ...]. *)

(* let's take a look at a common misadventure *)

Fixpoint length_acc (l : list) (length_so_far : Z) : Z :=
  match l with
  | nil => length_so_far
  | cons _ l' => length_acc l' (length_so_far + 1)
  end.
Definition length_using_acc l := length_acc l 0.

Lemma length_using_acc_correct : forall l,
  length_using_acc l = length l.
Proof.
  simplify.
  induction l; simplify; try equality.
  (* base case was solved *)
  unfold length_using_acc in *.
  simplify.
  (* This proof is stuck because *)
  (* - IHl talks about [length_using l 0] *)
  (* - Goal talks about [length_using l 1] *)
  (* there is no information to relate the two *)
Abort.

(* Root cause: length_acc x y calls length_acc with different y, so we
 * will need to  prove it correct for all y to prove it correct for y=0 *)

Lemma length_acc_correct : forall l acc,
  length_acc l acc = length l + acc.
Proof.
  simplify.
  induction l; simplify; try linear_arithmetic.
  (* base case was solved *)
  
  (* ... and yet we are still stuck. And for the same reason! *)
  (* - IHl talks about [length_using l acc] *)
  (* - Goal talks about [length_using l (acc+1)] *)
  (* there is no information to relate the two *)

  (* Even though the lemma statement says [forall acc], the
     induction hypothesis does not? Why? Let's see.. *)
  Show Proof.
  (* ... *)
  (* list_ind (fun l => length_acc l acc = length l + acc) *)
  (* ... *)
  (* So [P l := length l acc = length l + acc] *)

  Check list_ind.
  (* With this P, the induction lemma goes as follows: *)
  Check list_ind (fun l => length_acc l acc = length l + acc).
  (* 
    (* premise 1: *)
      ((( forall (h : Z) (l' : list),
          length_acc l' acc = length l' + acc ->
          length_acc (cons h l') acc = length (cons h l') + acc ))) ->
    (* premise 2: *)
      ((( length_acc nil acc = length nil + acc ))) ->
    (* conclusion:
      ((( forall l : list, length_acc l acc = length l + acc ))) *)
  *)
  (* Notably missing from the premises is [forall acc, ...] *)
  (* This is because [induct] inferred [P] from the goal *after*
     simplify had moved [acc] into the context, ignoring the context. *)
  (* Takeaway #1: think about [P] when doing induction. *)
  (* Takeaway #2: for [induct] to be predictable, call it as the first
       step of a proof, on the first [forall] quantified variable.
       Reorder variables to make that so. *)
Abort.

Lemma length_acc_correct : forall acc l, (* WRONG ORDER *)
  length_acc l acc = length l + acc.
Proof.
  induction l.
  Show Proof.
  (* list_ind (fun l : list => length_acc l acc = length l + acc) *)
  (* same problem, this time because [induct] moved [acc] to context *)
Abort.

Lemma length_acc_correct : forall l acc,
  length_acc l acc = length l + acc.
Proof.
  induct l.
  Show Proof.
  (* list_ind (fun l => forall acc, length_acc l acc = length l + acc *)
  all : simplify; try linear_arithmetic.
  rewrite IHl.
  all : simplify; try linear_arithmetic.
Qed.


(* practice: try to think of what the induction lemma for this inductive
 * looks like *)

Inductive frankeninductive :=
| leaf
    (a : nat)
    (b : Z)
    (c : nat * Z)
| through
    (x : nat)
    (SUBTREE : frankeninductive)
    (y : Z) 
| branch
    (x : nat)
    (LEFT RIGHT : frankeninductive)
    (y : Z) 
.

(* answer below... *)




























Check frankeninductive_ind.
(*first_friday_recitation.v
frankeninductive_ind (P : frankeninductive -> Prop) :

(* premise 1 *)
  (forall (a : nat)
          (b : Z)
          (c : nat * Z)
   , P (leaf a b c)) ->

(* premise 2 *)
  (forall (x : nat)
          (SUBTREE : frankeninductive), P SUBTREE ->
   forall (y : Z)
   , P (through x SUBTREE y)) ->

(* premise 3 *)
  (forall (x : nat)
          (LEFT : frankeninductive), P LEFT ->
   forall (RIGHT : frankeninductive), P RIGHT ->
   forall (y : Z)
   , P (branch x LEFT RIGHT y)) ->

(* conclusion *)
       forall f2 : frankeninductive, P f2
*)
