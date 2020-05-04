(** * 6.822 Formal Reasoning About Programs, Spring 2020 - Pset 12 *)

Require Import Frap.Frap.
Require Import Frap.MessagesAndRefinement.

Module Type S.

  Inductive request :=
  | GET (client_id key : nat).

  Definition get_key (req : request) : nat :=
    match req with
    | GET _ key => key
    end.

  Inductive response :=
  | FOUND (client_id key : nat) (value : nat)
  | NOT_FOUND (client_id key : nat).

  Definition request_handler (store : fmap nat nat) (source output : channel) : proc :=
    ??source(req: request);
    match req with
    | GET client_id key =>
      match store $? key with
      | Some v => !!output(FOUND client_id key v); Done
      | None => !!output(NOT_FOUND client_id key); Done
      end
    end.

  Definition split_store (full_store even_store odd_store : fmap nat nat) : Prop :=
    (forall k, k mod 2 = 0  -> even_store $? k = full_store $? k) /\
    (forall k, k mod 2 = 0  -> odd_store  $? k = None) /\
    (forall k, k mod 2 <> 0 -> even_store $? k = None) /\
    (forall k, k mod 2 <> 0 -> odd_store  $? k = full_store $? k).

  Definition request_dispatcher (input forward_even forward_odd : channel) : proc :=
    ??input(req: request);
    if get_key req mod 2 ==n 0 then
      !!forward_even(req); Done
    else
      !!forward_odd(req); Done.

  Definition balanced_handler (even_store odd_store : fmap nat nat) (input output : channel) : proc :=
    New[input; output](forward_even);
    New[input; output; forward_even](forward_odd);
    request_dispatcher input forward_even forward_odd
    || (request_handler even_store forward_even output)
    || (request_handler odd_store forward_odd output).

  Definition correctness: Prop := forall full_store even_store odd_store input output,
      split_store full_store even_store odd_store ->
      input <> output ->
      forall trace,
        couldGenerate (balanced_handler even_store odd_store input output) trace ->
        couldGenerate (request_handler full_store input output) trace.

  Parameter balanced_handler_correct : correctness.

End S.
