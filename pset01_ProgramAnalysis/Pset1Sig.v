(** * 6.822 Formal Reasoning About Programs, Spring 2020 - Pset 1 *)

Require Import Frap.
(* If this import command doesn't work, something may be wrong with the copy
 * of the FRAP book source that has been included as a Git submodule.
 * Running `git submodule init' or `git submodule update' in the repository
 * base directory might help.  However, it's also necessary to build the
 * book library, like so (starting from the base of this repository):
 * <<
     make -C frap lib
   >>
 * See below for installing Coq, which is a prerequisite for the above to work.
 *)

(* Authors:
 * Peng Wang (wangpeng@csail.mit.edu),
 * Adam Chlipala (adamc@csail.mit.edu),
 * Joonwon Choi (joonwonc@csail.mit.edu),
 * Benjamin Sherman (sherman@csail.mit.edu)
 * Andres Erbsen (andreser@csail.mit.edu)
 *)

(* This pset dives straight in to building a program-analysis pass and
 * proving it sound in Coq. But before that, you will need to get set up
 * with Coq. *)

(*
 * All the psets we provide should be compatible with several Coq versions,
 * including 8.9, 8.10, and 8.11.  If you haven't installed Coq before, we
 * encourage you to install the latest version, which is 8.11, though you
 * may also find it more convenient to install a package from your
 * operating system.  For instance:
 * - Coq has been included with Ubuntu <https://www.ubuntu.com/> for a while,
 *   and the last releases includes a new enough Coq version.
 *   Just run `apt-get install coq'.
 *   If your Ubuntu version is older than 19.10, don't install Coq from the
 *   Ubuntu repos, because otherwise you'll get a too old Coq version.
 * - Mac Homebrew <http://brew.sh/> also includes a new enough version.
 *   Just run `brew install coq'.
 *
 * To install from source, see the official download page:
 *   https://coq.inria.fr/download
 *
 * It will also be *essential* to install a UI for editing Coq proofs!
 * The course staff use and recommend Proof General <https://proofgeneral.github.io/>,
 * which is a mode for the Emacs IDE; or Coqtail, which is a similar vim plugin.
 * Both projects' GitHub pages include installation instructions. Some older versions,
 * say from OS packages, may work fine for this class, too.
 *
 * However, there is a standalone Coq IDE called, fittingly, CoqIDE, which
 * ships with Coq itself.  It has a less steep learning curve, though many of us
 * believe that Proof General supports more productive coding, after spending some
 * practice time.
 *
 * We will have special office hours the first week of class,
 * to help everyone get these packages set up.
 *
 * Now, on to the actual assignment, once you have Coq and a UI installed!
 *)

(* The first part of this assignment involves the [bool] datatype,
 * which has the following definition.
 * <<
     Inductive bool :=
     | true
     | false.
   >>
 * We will define logical negation and conjunction of Boolean values,
 * and we will prove some properties of these definitions.

 * In the second part of this assignment, we will work with a simple language
 * of imperative arithmetic programs that sequentially apply operations
 * to a natural-number-valued state.

 * The [Prog] datatype defines abstract syntax trees for this language.
 *)

Inductive Prog :=
  | Done                             (* Don't modify the state. *)
  | AddThen (n : nat) (p : Prog)     (* Add [n] to the state, then run [p]. *)
  | MulThen (n : nat) (p : Prog)     (* Multiply the state by [n], then run [p]. *)
  | DivThen (n : nat) (p : Prog)     (* Divide the state by [n], then run [p]. *)
  | VidThen (n : nat) (p : Prog)     (* Divide [n] by the state, then run [p]. *)
  | SetToThen (n : nat) (p : Prog)   (* Set the state to [n], then run [p]. *)
  .

(* Your job is to define a module implementing the following
 * signature.  We ask you to implement a file Pset1.v, where the skeleton is
 * already given, such that it can be checked against this signature by
 * successfully processing a third file (Pset1Check.v) with a command like so:
 * <<
    Require Pset1Sig Pset1.

    Module M : Pset1Sig.S := Pset1.
   >>
 * You'll need to build your module first, which the default target of our
 * handy Makefile does for you automatically.  Note that the _CoqProject
 * file included here is also important for making compilation and
 * interactive editing work.  Your Pset1.v file is what you upload to the course
 * web site to get credit for doing the assignment.
 *)

(* Finally, here's the actual signature to implement. *)
Module Type S.

  (* Define [Neg] so that it implements Boolean negation, which flips
   * the truth value of a Boolean value.
   *)
  Parameter Neg : bool -> bool.

  (* For instance, the negation of [true] should be [false].
   * This proof should follow from reducing both sides of the equation
   * and observing that they are identical.
   *)
  Axiom Neg_true : Neg true = false.

  (* Negation should be involutive, meaning that if we negate
   * any Boolean value twice, we should get the original value back.

   * To prove a fact like this that holds for all Booleans, it suffices
   * to prove the fact for both [true] and [false] by using the
   * [cases] tactic.
   *)
  Axiom Neg_involutive : forall b : bool, Neg (Neg b) = b.

  (* Define [And] so that it implements Boolean conjunction. That is,
   * the result value should be [true] exactly when both inputs
   * are [true].
   *)
  Parameter And : bool -> bool -> bool.

  (* Here are a couple of examples of how [And] should act on
   * concrete inputs.
   *)
  Axiom And_true_true : And true true = true.
  Axiom And_false_true : And false true = false.

  (* Prove that [And] is commutative, meaning that switching the order
   * of its arguments doesn't affect the result.
   *)
  Axiom And_comm : forall x y : bool, And x y = And y x.

  (* Prove that the conjunction of a Boolean value with [true]
   * doesn't change that value.
   *)
  Axiom And_true_r : forall x : bool, And x true = x.


  (* Define [run] such that [run p n] gives the final state
   * that running the program [p] should result in, when the
   * initial state is [n].
   * Use the +, *, and / operators for natural numbers provided
   * by the Coq standard library, and for this part of the
   * exercise, don't worry about division by 0, doing the same
   * thing as division from the standard library does is fine.
   *)
  Parameter run : Prog -> nat -> nat.

  Axiom run_Example1 : run Done 0 = 0.
  Axiom run_Example2 : run (MulThen 5 (AddThen 2 Done)) 1 = 7.
  Axiom run_Example3 : run (SetToThen 3 (MulThen 2 Done)) 10 = 6.

  (* Define [numInstructions] to compute the number of instructions
   * in a program, not counting [Done] as an instruction.
   *)
  Parameter numInstructions : Prog -> nat.

  Axiom numInstructions_Example :
    numInstructions (MulThen 5 (AddThen 2 Done)) = 2.

  (* Define [concatProg] such that [concatProg p1 p2] is the program
   * that first runs [p1] and then runs [p2].
   *)
  Parameter concatProg : Prog -> Prog -> Prog.

  Axiom concatProg_Example :
     concatProg (AddThen 1 Done) (MulThen 2 Done)
   = AddThen 1 (MulThen 2 Done).

  (* Prove that the number of instructions in the concatenation of
   * two programs is the sum of the number of instructions in each
   * program.
   *)
  Axiom concatProg_numInstructions : forall p1 p2,
      numInstructions (concatProg p1 p2)
      = numInstructions p1 + numInstructions p2.

  (* Prove that running the concatenation of [p1] with [p2] is
     equivalent to running [p1] and then running [p2] on the
     result. *)
  Axiom concatProg_run : forall p1 p2 initState,
      run (concatProg p1 p2) initState =
      run p2 (run p1 initState).

  (* As there is no intuitive or broadly useful definition for x/0,
     common processors handle it differently. We would like to model the
     portable behavior of a program, that is, its behavior to the extent
     it is known without relying on arbitrary choices about division by
     zero. The following interpreter returns (b, s), where the Boolean [b]
     indicates whether the execution completed without division by
     zero, and if it did, then [s] is the final state. First, you will be
     asked to prove that [s] matches [run] in those cases. *)
  Fixpoint runPortable (p : Prog) (state : nat) : bool * nat :=
    match p with
    | Done => (true, state)
    | AddThen n p => runPortable p (n+state)
    | MulThen n p => runPortable p (n*state)
    | DivThen n p =>
        if n ==n 0 then (false, state) else
        runPortable p (state/n)
    | VidThen n p =>
        if state ==n 0 then (false, 0) else
        runPortable p (n/state)
    | SetToThen n p =>
        runPortable p n
    end.

  Axiom runPortable_run : forall p s0 s1,
    runPortable p s0 = (true, s1) -> run p s0 = s1.

  (* Static analysis to validate that a program never divides by 0 *)

  (* The final goal of this pset is to implement [validate : Prog -> bool] *)
  Parameter validate : Prog -> bool.
  (* such that if this function returns [true], the program would not trigger
     division by zero regardless of what state it starts out in.  [validate] is
     allowed to return [false] for some perfectly good programs that never cause
     a division by zero, but it must recognize as good the examples given below.
     In jargon, [validate] is required to be sound but not complete, but
     "complete enough" for the use cases defined by the examples given here: *)
  Definition goodProgram1 := AddThen 1 (VidThen 10 Done).
  Definition goodProgram2 := AddThen 0 (MulThen 10 (AddThen 0 (DivThen 1 Done))).
  Definition goodProgram3 := AddThen 1 (MulThen 10 (AddThen 0 (VidThen 1 Done))).
  Definition goodProgram4 := Done.
  Definition goodProgram5 := SetToThen 0 (DivThen 1 Done).
  Definition goodProgram6 := SetToThen 1 (VidThen 1 Done).
  Definition goodProgram7 := AddThen 1 (DivThen 1 (DivThen 1 (VidThen 1 Done))).
  Axiom validate1 : validate goodProgram1 = true.
  Axiom validate2 : validate goodProgram2 = true.
  Axiom validate3 : validate goodProgram3 = true.
  Axiom validate4 : validate goodProgram4 = true.
  Axiom validate5 : validate goodProgram5 = true.
  Axiom validate6 : validate goodProgram6 = true.
  Axiom validate7 : validate goodProgram7 = true.

  Axiom validate_sound : forall p, validate p = true ->
    forall s, runPortable p s = (true, run p s).
End S.
