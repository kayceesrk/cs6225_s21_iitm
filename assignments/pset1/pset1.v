(**
 * PSet 1: Functional Programming in Coq

  This lab is designed as a file that you should download and complete in a Coq IDE.
  Before doing that, you need to install Coq.  The installation instructions
  are on the course website.
*)

(* Exercise: mult2 [10 points].
   Define a function that multiplies its input by 2.
   What is the function's type?
   What is the result of computing the function on 0?  On 3110?
*)

(* Exercise: xor [10 points].
   Define a function that computes the xor of two [bool] inputs.
   Do this by pattern matching on the inputs.
   What is the function's type?
   Compute all four possible combinations of inputs to test your function.
*)

(* Exercise: is_none [20 points].
   Define a function that returns [true] if its input is [None], and [false] otherwise.
   Your function's type should be [forall A : Type, option A -> bool].
   That means the function will actually need to take two inputs:
     the first has type [Type], and the second is an option.
   Hint:  model your solution on [is_empty] in the notes for this lecture.
*)

Require Import List.
Import ListNotations.

(* Exercise: double_all [20 points].
   There is a function [map] that was imported by the [Require Import List] command above.
   First, check its type with [Check map].  Explain that type in your own words.
   Second, print it with [Print map].  Note at the end of that which arguments are _implicit_.
   For a discussion of what implicit means, see the notes for this lecture.
   Third, use map to write your own function, which should double (i.e., multiply by 2)
   every value of a list.
   For example, [double_all [0;2;10]] should be [[0;4;20]].
*)

(* Exercise: sum [20 points]
   Write a function that sums all the natural numbers in a list.
   Implement this two different ways:
   - as a recursive function, using the [Fixpoint] syntax.
   - as a nonrecursive function, using [Definition] and an application of [fold_left].
*)

Inductive day : Type :=
  | sun : day
  | mon : day
  | tue : day
  | wed : day
  | thu : day
  | fri : day
  | sat : day.

Definition next_day d :=
  match d with
  | sun => mon
  | mon => tue
  | tue => wed
  | wed => thu
  | thu => fri
  | fri => sat
  | sat => sun
  end.

(* Exercise: thu after wed [20 points].
   State a theorem that says [thu] is the [next_day] after [wed].
   Write down in natural language how you would informally explain
   to a human why this theorem is true.
   ---> Don't skip this "natural language" part of the exercise;
        it's crucial to develop intuition before proceeding.
   Prove the theorem in Coq.
*)

(* Exercise: wed before thu [30 points].
   Below is a theorem that says if the day after [d] is [thu], then
   [d] must be [wed].
   Write down in natural language how you would informally explain
   to a human why this theorem is true.
   ---> Don't skip this "natural language" part of the exercise;
        it's crucial to develop intuition before proceeding.
   Prove the theorem in Coq.  To do that, delete the [Abort]
   command, which tells Coq to discard the theorem,
   then fill in your own proof.
*)

Theorem wed_proceeds_thu : forall d : day, next_day d = thu -> d = wed.
Abort.

(* Exercise: tl_opt [20 points].
   Define a function [tl_opt] such that [tl_opt lst] return [Some t] if [t] is the tail of [lst],
   or [None] if [lst] is empty.
   We have gotten you started by providing an obviously incorrect definition, below; you should
   replace the body of the function with a correct definition.
*)

Definition tl_opt {A : Type} (lst : list A) : option (list A) :=
  None.

(* Here is a new tactic: [rewrite x].  If [H: x = e] is an assumption in the
   proof state, then [rewrite H] replaces [x] with [e] in the subgoal being proved.  For example,
   here is a proof that incrementing 1 produces 2: *)

Theorem inc1_is_2 : forall n, n=1 -> (fun x => x+1) n = 2.
Proof.
  intros n n_is_1. rewrite n_is_1. trivial.
Qed.

(* Exercise: tl_opt correct [20 points].
   Using [rewrite], prove the following theorems. For both, first explain in natural language
   why the theorem should hold, before moving on to prove it with Coq. *)

Theorem nil_implies_tlopt_none :
  forall A : Type, forall lst : list A,
  lst = nil -> tl_opt lst = None.
Abort.

Theorem cons_implies_tlopt_some :
  forall {A : Type} (h:A) (t : list A) (lst : list A),
  lst = h::t -> tl_opt lst = Some t.
Abort.
