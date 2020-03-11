(** * 6.822 Formal Reasoning About Programs, Spring 2020 - Pset 6 *)
Require Import Frap AbstractInterpret.

Inductive domain :=
| Exactly (n : nat)
| Anything.

Definition represents (x:nat) (d:domain) : Prop :=
  match d with
  | Exactly n => x = n
  | Anything => True
  end.

Definition absint_binop (f : nat -> nat -> nat) (a b : domain) : domain :=
  match a, b with
  | Exactly n, Exactly m => Exactly (f n m)
  | _, _ => Anything
  end.

Definition join (a b : domain) : domain :=
  match a, b with
  | Exactly n, Exactly m => if n ==n m then Exactly n else Anything
  | _, _ => Anything
  end.

Definition constant_absint := {|
  Top := Anything;
  Constant := Exactly;
  Add := absint_binop Nat.add;
  Subtract := absint_binop Nat.sub;
  Multiply := absint_binop Nat.mul;
  Join := join;
  Represents := represents
|}.

Inductive constfold_result :=
| Known (n : nat)
| Simplified (e : arith).

Definition to_arith (r : constfold_result) : arith :=
  match r with
  | Known n => Const n
  | Simplified e => e
  end.

(* 10% for specification, 15% for proof *)
Fixpoint constfold_arith (e : arith) (s : astate constant_absint) : constfold_result :=
  match e with
  | Const n => Known n
  | Var x =>
    match s $? x with
    | Some (Exactly n) => Known n
    | _ => Simplified e
    end
  | Plus e1 e2 =>
    match constfold_arith e1 s, constfold_arith e2 s with
    | Known n1, Known n2 => Known (n1 + n2)
    | e1', e2' => Simplified (Plus (to_arith e1') (to_arith e2'))
    end
  | Times e1 e2 =>
    match constfold_arith e1 s, constfold_arith e2 s with
    | Known n1, Known n2 => Known (n1 * n2)
    | e1', e2' => Simplified (Times (to_arith e1') (to_arith e2'))
    end
  | Minus e1 e2 =>
    match constfold_arith e1 s, constfold_arith e2 s with
    | Known n1, Known n2 => Known (n1 - n2)
    | e1', e2' => Simplified (Minus (to_arith e1') (to_arith e2'))
    end
  end.

(* 10% for specification, 15% for proof *)
Fixpoint constfold_cmd (c : cmd) (ss : astates constant_absint) (C : cmd -> cmd) : cmd :=
  match c with
  | Skip => Skip
  | Assign x e =>
    match ss $? C c with
    | None => Assign x e
    | Some s => Assign x (to_arith (constfold_arith e s))
    end
  | Sequence c1 c2 => Sequence (constfold_cmd c1 ss (fun c' => C (Sequence c' c2)))
                               (constfold_cmd c2 ss C)
  | If e then_ else_ =>
    If e (constfold_cmd then_ ss C)
         (constfold_cmd else_ ss C)
  | While e body =>
    While e (constfold_cmd body ss (fun c' => C (Sequence c' c)))
  end.

Definition compatible_throughout_steps {A} ss v c:= forall c' s v',
  ss $? c' = Some s -> step^* (v, c) (v', c') -> @compatible A s v'.

Module Type S.
  (* 20% *)
  Axiom constant_sound : absint_sound constant_absint.

  (* 15% *)
  Axiom constfold_steps : forall v c v' c',
    step^* (v, c) (v', c') ->
    forall ss, compatible_throughout_steps ss v c ->
    step^* (v, constfold_cmd c ss (fun c1 => c1))
    (v', constfold_cmd c' ss (fun c1 => c1)).

  (* 15% *)
  Axiom eval_constfold : forall v c v',
    eval v c v' ->
    forall ss, compatible_throughout_steps ss v c ->
    eval v (constfold_cmd c ss (fun c1 => c1)) v'.
End S.
