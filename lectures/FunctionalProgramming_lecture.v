(* Types and Functions *)

Inductive day : Type :=
| sun : day
| mon : day
| tue : day
| wed : day
| thu : day
| fri : day
| sat : day.

Let next_day d :=
  match d with
  | sun => mon
  | mon => tue
  | tue => wed
  | wed => thu
  | thu => fri
  | fri => sat
  | sat => sun
  end.

Definition prev_day d :=
  match d with
  | sun => sat
  | mon => sun
  | tue => mon
  | wed => tue
  | thu => wed
  | fri => thu
  | sat => fri
  end.

(* Theorems and proofs *)

Theorem wed_after_tue : next_day tue = wed.
Proof.
  auto.
Qed.

Print wed_after_tue.

(* eq_refl -- from Coq stdlib. Says "Equality is reflexive" *)

Theorem wed_after_tue' : next_day tue = wed.
Proof.
  (* new tactics -- simpl, trivial *)
  
  simpl. trivial.
Qed.

Print wed_after_tue'.
(* same proof as using [auto] *)


(* The day of the week never repeats. *)
Theorem day_never_repeats : forall d : day, next_day d <> d.

Proof. auto. (* stuck? *)

  (* new tactics -- intros, destruct, discriminate *)

  intros d. destruct d.
  simpl. discriminate.
  simpl. discriminate.
  simpl. discriminate.
  simpl. discriminate.
  simpl. discriminate.
  simpl. discriminate.
  simpl. discriminate.

Qed.

(* Same as previous; avoid tedium *)
Theorem day_never_repeats' : forall d : day, next_day d <> d.
Proof.
  intros d. destruct d.
  all: discriminate.
  (* discriminate does simplification as well! *)
Qed.


(* Introduce a "tactical" ; which combines tactics *)
Theorem day_never_repeats'' : forall d : day, next_day d <> d.
Proof.
  intros d. destruct d; discriminate.
Qed.

Theorem mon_preceds_tues : forall d : day,
  next_day d = tue -> d = mon.

(* What's the intuitive proof? 
   - Consider every day one by one
   - precondition (LHS of implication) is false in 6 cases. Hence, holds.
   - The other d is mon.
*)
Proof.
  (* naming introductions explicitly *)
  intros d next_day_is_tue.
  destruct d; discriminate || trivial.

  (* || is a tactical. In t1 || t2, if t1 fails, then try t2. *)
Qed.

(**********************************************************************)


(* Lists *)

(* Import full list library; by default some parts are included *)
Require Import List.
Import ListNotations.


Module MyList. (* We can have modules within files *)

Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

End MyList.

(* What is the Coq stdlib definition of "list" *)
Check list.
(* [list] is a type constructor *)

Definition is_empty (A : Type) (lst : list A) :=
  match lst with
  | nil => true
  | cons _ _ => false
  end.
(* Need explicit types for [is_empty]. Coq's type system _vastly_ more
   expressive than OCaml's. Type inference is not possible always. *)

Definition is_empty_sugar (A : Type) (lst : list A) :=
  match lst with
  | [] => true
  | _::_ => false
  end.
(* [], :: are syntactic sugar for list constructors nil and cons *)

Compute is_empty nat [1].

Compute is_empty nat [].

(* Implicit arguments -- infer type from context; mostly works) *)
Definition is_empty' {A : Type} (lst : list A) :=
  match lst with
  | [] => true
  | _::_ => false
  end.

Compute is_empty' [1].

Check is_empty'.

Compute @is_empty' nat [1]. (* provide implcit argument explicitly! *)


Module MyLength.

(* Fixpoint in Coq = let rec in OCaml *)
Fixpoint length {A : Type} (lst : list A) :=
  match lst with
  | nil => 0
  | _::t => 1 + length t
  end.

Compute length [1;2].

End MyLength.

(**********************************************************************)

(* Options *)

Module MyOption.

Inductive option (A:Type) : Type :=
  | Some : A -> option A
  | None : option A.

End MyOption.

Definition hd_opt {A : Type} (lst : list A) : option A :=
  match lst  with
  | nil => None
  | x :: _ => Some x
  end.

Compute hd_opt [1].

Compute hd_opt [].

Compute @hd_opt nat [].

(* When [hd_opt] is applied to a list of length 0, it returns [None]. *)
Theorem length0_implies_hdopt_is_none :
  forall A : Type, forall lst : list A,
    length lst = 0 -> hd_opt lst = None.
Proof.
  intros A lst length_lst_is_0.
  destruct lst.
    simpl. trivial. (* trivial does simplification *)
    simpl in length_lst_is_0. discriminate.
Qed.

Theorem length0_implies_hdopt_is_none' :
forall A : Type, forall lst : list A,
  length lst = 0 -> hd_opt lst = None.
Proof.
  intros A lst length_lst_is_0.
  destruct lst.
    - trivial.
    - discriminate. (* skipped explicit simplification *)
Qed.

(** The characters [+] and [*] can also be used as bullets, as can [--], [---],
etc.

(**********************************************************************)

** Summary

- Coq is a proof assistant
  + Includes a OCaml like FP langauge (Gallina)
  + Type system more advanced than OCaml
  + Tactic language (Ltac) for proving things about programs
  + Simple proofs about lists and options
*)
