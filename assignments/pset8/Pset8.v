(* No points will be awarded for Theorems/Lemmas using previous Admitted
* Theorems/Lemmas *)

Require Import Frap Pset8Sig.

Set Implicit Arguments.

(* 10 points *)
Lemma subtype_refl : forall t1, t1 $<: t1.
Proof.
Admitted.

(* 10 points *)
Lemma subtype_trans : forall t1 t2 t3, t1 $<: t2 -> t2 $<: t3 -> t1 $<: t3.
Proof.
Admitted.

(******************************************************************************)
(** Progress *)
(******************************************************************************)

(* canonical forms of well-typed values *)

(* 10 points *)
Lemma canonical_Fun v t1 t2 :
  hasty $0 v (Fun t1 t2) ->
  value v ->
  exists x e',
    v = Abs x e'.
Proof.
Admitted.

(* 10 points *)
Lemma canonical_TupleCons v t1 t2 :
  hasty $0 v (TupleTypeCons t1 t2) ->
  value v ->
  exists v1 v2,
    v = TupleCons v1 v2 /\
    value v1 /\
    value v2.
Proof.
Admitted.

(* 10 points *)
Lemma progress : forall e t,
    hasty $0 e t
    -> value e
      \/ (exists e' : exp, step e e').
Proof.
Admitted.

(******************************************************************************)
(** Preservation *)
(******************************************************************************)

(* 10 points *)
Lemma weakening_override : forall V G G' (x : var) (t : V),
    (forall x' t', G $? x' = Some t' -> G' $? x' = Some t')
    -> (forall x' t', G $+ (x, t) $? x' = Some t'
                -> G' $+ (x, t) $? x' = Some t').
Proof.
Admitted.

(* 10 points *)
Lemma weakening : forall G e t,
    hasty G e t
    -> forall G', (forall x t, G $? x = Some t -> G' $? x = Some t)
            -> hasty G' e t.
Proof.
Admitted.

(* 10 points *)
Lemma substitution : forall G x t' e t,
    hasty (G $+ (x, t')) e t ->
    forall e',
      hasty $0 e' t' ->
      hasty G (subst e' x e) t.
Proof.
Admitted.

(* 10 points *)
Lemma preservation0 : forall e1 e2,
    step0 e1 e2
    -> forall t, hasty $0 e1 t
           -> hasty $0 e2 t.
Proof.
Admitted.

(* 10 points *)
Lemma generalize_plug : forall e1 C e1',
    plug C e1 e1'
    -> forall e2 e2', plug C e2 e2'
                -> (forall t, hasty $0 e1 t -> hasty $0 e2 t)
                -> (forall t, hasty $0 e1' t -> hasty $0 e2' t).
Proof.
Admitted.

(* 10 points *)
Lemma preservation : forall e1 e2,
    step e1 e2
    -> forall t, hasty $0 e1 t
           -> hasty $0 e2 t.
Proof.
Admitted.


(******************************************************************************)
(** Safety *)
(******************************************************************************)

(* 10 points *)
Theorem safety :
  forall e t,
    hasty $0 e t -> invariantFor (trsys_of e)
                                 (fun e' => value e'
                                            \/ exists e'', step e' e'').
Proof.
Admitted.
