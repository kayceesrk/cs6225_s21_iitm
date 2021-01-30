(** CS6225 -- Problem Set 4a (100 points) *)

(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 1 *)

Require Import Frap.

(* Authors:
 * Peng Wang (wangpeng@csail.mit.edu),
 * Adam Chlipala (adamc@csail.mit.edu),
 * Joonwon Choi (joonwonc@csail.mit.edu),
 * Benjamin Sherman (sherman@csail.mit.edu)
 *)

(* In this assignment, we will work with a simple language
 * of imperative arithmetic programs that sequentially apply operations
 * to a natural-number-valued state.

 * The [Prog] datatype defines abstract syntax trees for this language.
 *)

Inductive Prog :=
  | Done                             (* Don't modify the state. *)
  | AddThen (n : nat) (p : Prog)     (* Add [n] to the state, then run [p]. *)
  | MulThen (n : nat) (p : Prog)     (* Multiply the state by [n], then run [p]. *)
  | SetToThen (n : nat) (p : Prog)   (* Set the state to [n], then run [p]. *)
  .

(* Your job is to define a module implementing the following
 * signature.  We ask you to implement a file Pset4a.v, where the skeleton is
 * already given, such that it can be checked against this signature by
 * successfully processing a third file (Pset4aCheck.v) with a command like so:
 * <<
    Require Pset4aSig Pset4a.

    Module M : Pset4aSig.S := Pset4a.
   >>
 * You'll need to build your module first, which the default target of our
 * handy Makefile does for you automatically. Just issue [make] in this
 * directory.
 *
 * Note that the _CoqProject file included here is also important for making
 * compilation and interactive editing work.  Your Pset4a.v file is what you
 * upload to the course web site to get credit for doing the assignment.
 *)

(* Finally, here's the actual signature to implement. *)
Module Type S.

  (* Define [run] such that [run p n] gives the final state
   * that running the program [p] should result in, when the
   * initial state is [n].
   *)
  Parameter run : Prog -> nat -> nat.
  (* 10 points *)

  Axiom run_Example1 : run Done 0 = 0.
  Axiom run_Example2 : run (MulThen 5 (AddThen 2 Done)) 1 = 7.
  Axiom run_Example3 : run (SetToThen 3 (MulThen 2 Done)) 10 = 6.
  (* 10 points *)

  (* Define [numInstructions] to compute the number of instructions
   * in a program, not counting [Done] as an instruction.
   *)
  Parameter numInstructions : Prog -> nat.
  (* 10 points *)

  Axiom numInstructions_Example :
    numInstructions (MulThen 5 (AddThen 2 Done)) = 2.
  (* 10 points *)

  (* Define [concatProg] such that [concatProg p1 p2] is the program
   * that first runs [p1] and then runs [p2].
   *)
  Parameter concatProg : Prog -> Prog -> Prog.
  (* 10 points *)

  Axiom concatProg_Example :
     concatProg (AddThen 1 Done) (MulThen 2 Done)
   = AddThen 1 (MulThen 2 Done).
  (* 10 points *)

  (* Prove that the number of instructions in the concatenation of
   * two programs is the sum of the number of instructions in each
   * program.
   *)
  Axiom concatProg_numInstructions : forall p1 p2,
      numInstructions (concatProg p1 p2)
      = numInstructions p1 + numInstructions p2.
  (* 20 points *)

  (* Prove that running the concatenation of [p1] with [p2] is
     equivalent to running [p1] and then running [p2] on the
     result. *)
  Axiom concatProg_run : forall p1 p2 initState,
      run (concatProg p1 p2) initState =
      run p2 (run p1 initState).
  (* 20 points *)
End S.
