(**
* PSet 2 : Logic in Coq [360 points]
*)

(* Exercise: types [10 points].
Using [Definition], define a value of each of the following types:
- [nat]
- [Set]
- [0 * 1 = 0]  (* hint: [eq_refl] *)
- [Prop]
- [Type]
*)

Definition t1 : nat := (* FILL IN *).
Definition t2 : Set := (* FILL IN *).
Definition t3 : 0*1 = 0 := (* FILL IN *).
Definition t4 : Prop := (* FILL IN *).
Definition t5 : Type := (* FILL IN *).

(* Exercise: implication [20 points].
Prove the following theorems.  State English intuition before starting the Coq
proof.  When you're done with the Coq proof, revisit the intuition and see
whether you still agree with it; revise if necessary.
Hint: intros, apply, and/or assumption.
*)

Theorem imp1 : forall P Q : Prop,
  P -> (Q -> P).
(* Intuition: FILL IN *)
Proof.
  (* FILL IN *)
Qed.

Theorem imp2 : forall P Q R : Prop,
  (P -> (Q -> R)) -> (Q -> (P -> R)).
(* Intuition: FILL IN*)
Proof.
  (* FILL IN *)
Qed.


(* Exercise: implication program [20 points].
Look at the printed value of the following theorem. Explain in your own words
the functional program you see, as if you were writing English intuition for the
theorem.
*)

Theorem imp3 : forall P Q R : Prop,
  ((P -> Q) -> (P -> R)) -> (P -> (Q -> R)).
Proof.
  intros P Q R evPQPR evP evQ.
  apply evPQPR.
  - intros evPagain. assumption.
  - assumption.
Qed.

Print imp3.

(* Intuition: FILL IN *)

(* Exercise: conjunction [20 points].
Prove the following theorems.  State English intuition before starting the Coq
proof.
Hint: intros, apply, split, destruct, and/or assumption.
*)

Theorem conj1 : forall P Q : Prop,
  P -> (Q -> (P /\ Q)).
(* Intuition: FILL IN *)
Proof.
  (* FILL IN *)
Qed.

Theorem conj2 : forall P Q R : Prop,
  (P -> (Q -> R)) -> ((P /\ Q) -> R).
(* Intuition: FILL IN *)
Proof.
  (* FILL IN *)
Qed.

(* Exercise: conjunction associative [20 points].
Prove the following theorem. *)

Theorem conj3 : forall P Q R : Prop,
  (P /\ (Q /\ R)) -> ((P /\ Q) /\ R).
(* Intuition: FILL IN*)
Proof.
  (* FILL IN *)
Qed.

(* Exercise: direct proof conjunction associative [20 points].
The following definition gives a program that directly proves that conjunction
is associative.  (And it's likely though not certain that it's the same program
you produced in the previous exercise using tactics.)  Rewrite the program so
that it still proves the theorem, but doesn't use a nested pattern match.
Hint: deep pattern matching with conj.
*)

Definition direct_conj3 (P Q R : Prop) (evP_QR : P /\ Q /\ R)
  : (P /\ Q) /\ R
:=
match evP_QR with
| conj evP evQR =>
  match evQR with
  | conj evQ evR => conj (conj evP evQ) evR
  end
end.

Definition direct_conj3' (P Q R : Prop) (evP_QR : P /\ Q /\ R)
  : (P /\ Q) /\ R
:=
(* FILL IN*)
.

(* Exercise: disjunction [20 points].
Prove the following theorems.  State English intuition before starting the Coq
proof.
Hint: intros, left, right, apply, split, destruct, and/or assumption.
*)

Theorem disj1 : forall P : Prop,
  P -> P \/ P.
(* Intuition: FILL IN *)
Proof.
  (* FILL IN *)
Qed.

(* give a different proof, resulting in a different program,
   than the one you gave for [disj1]. *)
Theorem disj1' : forall P : Prop,
  P -> P \/ P.
(* Intuition: FILL IN *)
Proof.
  (* FILL IN *)
Qed.

Theorem disj2 : forall P : Prop,
  P \/ P -> P.
(* Intuition: FILL IN *)
Proof.
  (* FILL IN *)
Qed.

Theorem disj3 : forall P Q R : Prop,
  (P -> R) -> (Q -> R) -> (P \/ Q -> R).
(* Intuition: FILL IN *)
Proof.
  (* FILL IN *)
Qed.

(* Exercise: and distributes over or [30 points].
In the notes we prove that \/ distributes over /\.  Now state and
prove a theorem that shows /\ distributes over \/.
*)

Theorem and_distr_or : forall P Q R,
  P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
(* Intuition: FILL IN *)
Proof.
  (* FILL IN *)
Qed.

(* Exercise: true and false [20 points].
Prove the following theorems. The second uses a new connective,
[P <-> Q], which means [(P -> Q) /\ (Q -> P)], i.e., "if and only if" or
"iff".
Hint: intros, left/right, exact, split, assumption, apply, destruct.
You also might find [unfold iff] helpful. *)

Theorem tf1 : True \/ False.
(* Intuition: FILL IN *)
Proof.
  (* FILL IN *)
Qed.

Locate "<->".
Print iff.

Theorem tf2 : forall P : Prop,
  P <-> (True <-> P).
(* Intuition: FILL IN*)
Proof.
  (* FILL IN *)
Qed.

(* Exercise: negation [20 points].  *)

Theorem neg1 : forall P : Prop,
  P /\ ~P -> False.
(* Intuition: FILL IN *)
Proof.
  (* FILL IN *)
Qed.

(* This theorem is known as reasoning by _contrapositive_ *)
Theorem neg2 : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
(* Intuition:  FILL IN *)
Proof.
  (* FILL IN *)
Qed.

(* Exercise: de Morgan [30 points].  *)

(* This theorem is the "backwards" direction of DeMorgan2 from the
   notes, and this direction is actually provable in constructive logic. *)
Theorem neg3 : forall P Q : Prop,
  ~P \/ ~Q -> ~(P /\ Q).
(* Intuition: FILL IN *)
Proof.
  (* FILL IN *)
Qed.


(* Exercise: double negation of excluded middle [30 points].
Hint: go right, then go left. *)

Theorem dbl_neg_ex_middle : forall P : Prop,
  ~~(P \/ ~P).
(* Intuition: FILL IN (warning: it takes longer to explain
   this proof than it does to write it). *)
Proof.
  (* FILL IN *)
Qed.

(* Exercise: xor [40 points].
Define your own inductive type for exclusive or.
Prove that [P] xor [Q] holds iff [(P \/ Q) /\ (~P \/ ~Q)] holds.

Hints:
- The [left] and [right] tactics will work on any inductive type
  with two constructors.
- You will likely need a new tactic [inversion], which is like
  [destruct] except that it will also remember the original
  formula you are destructing, keeping that formula as part of the
  assumptions.
*)

(* FILL IN *)

(**
 * Proofs are Programs [60 points].
 *)

(*
For the following prove them by directly writing down the Coq program that is
the proof, rather than using tactics to help construct the proof.
  (A -> B) -> ((B -> C) -> (A -> C))
  A -> (A \/ B)
  B -> (A \/ B)
  (A -> C) -> ((B -> C) -> ((A \/ B) -> C))
  A /\ B -> A
  A /\ B -> B
  (C -> A) -> ((C -> B) -> (C -> (A /\ B)))
  (A -> (B -> C)) -> ((A /\ B) -> C)
  ((A /\ B) -> C) -> (A -> (B -> C))
  (A /\ ~A) -> B
  (A -> (A /\ ~A)) -> ~A
  A -> (A -> B) -> B

Here's an example of what we mean, using the first proposition
from above:
*)

Definition example : forall A B C : Prop,
  (A -> B) -> ((B -> C) -> (A -> C))
:=
  fun (A B C : Prop) (ab : A -> B) (bc : B -> C) (a : A) =>
    bc (ab a).

(* You will need to use pattern matching for proofs/programs involving
   conjunction, disjunction, and negation.  Specifically, [conj] will
   be useful for conjunction, [or_introl] and [or_intror] for disjunction,
   and [not] and [False_rect] for negation.  You can review those
   by examing the output of these: *)

Print and.
Print or.
Print not.
Print False_rect.
