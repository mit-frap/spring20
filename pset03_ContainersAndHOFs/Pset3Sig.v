(** * 6.822 Formal Reasoning About Programs, Spring 2020 - Pset 3 *)

Require Import Frap.Frap.


(* Here's a technical note on why this pset overrides a Frap tactic.
   There's no need to understand this at all.

   The "simplify" tactic provided by the Frap library is not quite suitable for this
   pset, because it does "autorewrite with core in *" (which we commented out below),
   and there's a Hint in Coq.Program.Combinators

        Hint Rewrite <- @compose_assoc : core.

   which causes "autorewrite with core in *." to have the
   same effect as

   rewrite <-? Combinators.compose_assoc.

   and apparently, rewrite does not just syntactic matching,
   but matching modulo unification, so we it will replace
   our "compose" by "Basics.compose", and rewrite using
   associativity of "compose" as many times as it can.
   It's confusing to have "Basics.compose" appear in our goals,
   and rewriting with associativity is something we want to teach in this
   pset, so we redefine "simplify" to not use "autorewrite": *)
Ltac simplify ::=
  repeat (unifyTails; pose proof I); repeat match goal with
                                            | H:True |- _ => clear H
                                            end;
   repeat progress (simpl in *; intros(*; try autorewrite with core in * *); simpl_maps);
   repeat normalize_set || doSubtract.



Module Type S.
  Inductive tree {A} :=
  | Leaf
  | Node (l : tree) (d : A) (r : tree).
  Arguments tree : clear implicits.

  Fixpoint flatten {A} (t : tree A) : list A :=
    match t with
    | Leaf => []
    | Node l d r => flatten l ++ d :: flatten r
    end.

  Definition either {A} (xo yo : option A) : option A :=
    match xo with
    | None => yo
    | Some x => Some x
    end.


  (* 1a) Simple containers *)

  (* 2 Points *)
  Parameter either_None_right : forall {A : Type} (xo : option A), either xo None = xo.

  (* 2 Points *)
  Parameter either_assoc :
    forall {A : Type} (xo yo zo : option A), either (either xo yo) zo = either xo (either yo zo).

  (* 1 Point *)
  Parameter head : forall {A : Type}, list A -> option A.

  (* 1 Point *)
  Parameter head_example : head (1 :: 2 :: 3 :: nil) = Some 1.

  (* 2 Points *)
  Parameter either_app_head :
    forall {A : Type} (xs ys : list A), head (xs ++ ys) = either (head xs) (head ys).

  (* 3 Points *)
  Parameter leftmost_Node : forall {A : Type}, tree A -> option A.

  (* 2 Points *)
  Parameter leftmost_Node_example : leftmost_Node (Node (Node Leaf 2 (Node Leaf 3 Leaf)) 1 Leaf) = Some 2.

  (* 5 Points *)
  Parameter leftmost_Node_head : forall {A : Type} (t : tree A), leftmost_Node t = head (flatten t).


  (* 1b) binary tries *)

  Definition binary_trie A := tree (option A).

  (* 3 Points *)
  Parameter lookup : forall {A : Type}, list bool -> binary_trie A -> option A.

  (* 1 Point *)
  Parameter lookup_example1 : lookup nil (Node Leaf (None : option nat) Leaf) = None.

  (* 1 Point *)
  Parameter lookup_example2 :
    lookup (false :: true :: nil)
           (Node (Node Leaf (Some 2) Leaf) None (Node (Node Leaf (Some 1) Leaf) (Some 3) Leaf)) =
    Some 1.

  (* 1 Point *)
  Parameter lookup_empty : forall {A : Type} (k : list bool), lookup k (Leaf : binary_trie A) = None.

  (* 3 Points *)
  Parameter insert : forall {A : Type}, list bool -> option A -> binary_trie A -> binary_trie A.

  (* 1 Point *)
  Parameter insert_example1 : lookup nil (insert nil None (Node Leaf (Some 0) Leaf)) = None.

  (* 1 Point *)
  Parameter insert_example2 :
    lookup nil (insert (true :: nil) (Some 2) (Node Leaf (Some 0) Leaf)) = Some 0.

  (* 12 Points *)
  Parameter lookup_insert :
    forall {A : Type} (k : list bool) (v : option A) (t : binary_trie A), lookup k (insert k v t) = v.


  (* 2a) HOFs: id and compose *)

  Definition id {A : Type} (x : A) : A := x.
  Definition compose {A B C : Type} (g : B -> C) (f : A -> B) (x : A) : C := g (f x).

  (* 1 Point *)
  Parameter compose_id_l : forall (A B : Type) (f : A -> B), compose id f = f.

  (* 1 Point *)
  Parameter compose_id_r : forall (A B : Type) (f : A -> B), compose f id = f.

  (* 1 Point *)
  Parameter compose_assoc :
    forall (A B C D : Type) (f : A -> B) (g : B -> C) (h : C -> D),
      compose h (compose g f) = compose (compose h g) f.

  Fixpoint selfCompose{A: Type}(f: A -> A)(n: nat): A -> A :=
    match n with
    | O => id
    | S n' => compose f (selfCompose f n')
    end.

  (* 3 Points *)
  Parameter exp : nat -> nat -> nat.
  Parameter test_exp_2_3 : exp 2 3 = 8.
  Parameter test_exp_3_2 : exp 3 2 = 9.
  Parameter test_exp_4_1 : exp 4 1 = 4.
  Parameter test_exp_5_0 : exp 5 0 = 1.
  Parameter test_exp_1_3 : exp 1 3 = 1.

  (* 5 Points *)
  Parameter map_id : forall {A : Type} (xs : list A), List.map id xs = xs.

  (* 5 Points *)
  Parameter map_compose :
    forall (A B C : Type) (g : B -> C) (f : A -> B) (xs : list A),
      List.map (compose g f) xs = List.map g (List.map f xs).


  (* 2b) HOFs: tree_map *)

  (* 3 Points *)
  Parameter tree_map : forall {A B : Type}, (A -> B) -> tree A -> tree B.

  (* 1 Point *)
  Parameter tree_map_example :
    tree_map (fun x : nat => x + 1) (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 (Node Leaf 4 Leaf))) =
    Node (Node Leaf 2 Leaf) 3 (Node Leaf 4 (Node Leaf 5 Leaf)).

  (* 10 Points *)
  Parameter tree_map_flatten :
    forall (A B : Type) (f : A -> B) (t : tree A), flatten (tree_map f t) = List.map f (flatten t).


  (* 2c) HOFs: inverse functions *)

  Definition inverse{A B: Type}(f: A -> B)(g: B -> A): Prop := compose g f = id.

  (* 3 Points *)
  Parameter plus2minus2 : inverse (fun x : nat => x + 2) (fun x : nat => x - 2).

  (* 4 Points *)
  Parameter minus2plus2 : ~ inverse (fun x : nat => x - 2) (fun x : nat => x + 2).

  (* 1 Point *)
  Parameter inverse_id : forall {A : Type}, inverse (@id A) (@id A).

  (* 7 Points *)
  Parameter invert_map :
    forall (A B : Type) (f : A -> B) (g : B -> A), inverse f g -> inverse (List.map f) (List.map g).

  (* 14 Points *)
  Parameter invert_selfCompose :
    forall {A : Type} (f g : A -> A) (n : nat), inverse f g -> inverse (selfCompose f n) (selfCompose g n).

End S.
