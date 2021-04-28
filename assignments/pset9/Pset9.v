(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 7 *)

Require Import Frap Pset9Sig.

(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 7 *)

(** KC: Use can use admitted lemmas in subsequent proofs and 
    get the full points for that proof or lemma. For example,
    you can prove the theorem [validator_ok] towards the end 
    without proving other lemmas and get 5 ponints. *)


Require Import Frap Pset9Sig.

Ltac iffer :=
  match goal with
  | [H : context [if ?e then _ else _] |- _] => cases e; try equality
  end.

Ltac matcher :=
  match goal with
  | [H : context [match ?e with _ => _ end] |- _] => cases e; try equality
  end.

Ltac split_and :=
  match goal with
  | [H : _ && _ = true |- _] => apply andb_true_iff in H; destruct H
  end.

Ltac invert_Some :=
  match goal with
  | [H : Some _ = Some _ |- _] => invert H
  end.

Definition sameValuationExcept (v1 v2: valuation) (md: maydiff) :=
  forall x, md $? x = None -> v1 $? x = v2 $? x.

(* 5 points *)
Lemma arithNotReading_ok:
  forall e md v1 v2,
    arithNotReading e md = true ->
    sameValuationExcept v1 v2 md ->
    interp e v1 = interp e v2.
Proof.
Admitted.

(* 5 points *)
Lemma sameValuationExcept_add:
  forall v1 v2 md x v,
    sameValuationExcept v1 v2 md ->
    md $? x = None ->
    sameValuationExcept (v1 $+ (x, v)) (v2 $+ (x, v)) md.
Proof.
Admitted.

(* 5 points *)
Lemma sameValuationExcept_md_add:
  forall v1 v2 md x v v',
    sameValuationExcept v1 v2 md ->
    sameValuationExcept v1 (v2 $+ (x, v)) (md $+ (x, v')).
Proof.
Admitted.

Hint Immediate includes_refl.

(* 2 points *)
Lemma cmd_eq_dec_refl {A} : forall c (t f : A),
    (if cmd_eq_dec c c then t else f) = t.
Proof.
Admitted.

Ltac rewrite_cmd_eq_dec_refl :=
  match goal with
  | [H : context[if cmd_eq_dec ?c ?c then _ else _] |- _] => rewrite cmd_eq_dec_refl in H
  end.

(* 5 points *)
Lemma validator_same_true_md:
  forall c md nmd,
    validator' c c md = Some nmd -> md = nmd.
Proof.
Admitted.

(* 20 points *)
Lemma validator_step0_ok:
  forall c1 c2 md fmd,
    validator' c1 c2 md = Some fmd ->
    forall v1 v2,
      sameValuationExcept v1 v2 md ->
      forall l v1' c1',
        step0 (v1, c1) l (v1', c1') ->
        exists vc2',
          step0 (v2, c2) l vc2' /\
          (exists nmd,
              validator' c1' (snd vc2') nmd = Some fmd /\
              sameValuationExcept v1' (fst vc2') nmd).
Proof.
Admitted.

(* 5 points *)
Lemma cstep_Sequence:
  forall l v c1 c2 v' c1',
    cstep (v, c1) l (v', c1') ->
    cstep (v, c1 ;; c2) l (v', c1' ;; c2).
Proof.
Admitted.

(* 20 points *)
Lemma validator_stepc_ok:
  forall C c c1,
    plug C c c1 ->
    forall c2 md fmd,
      validator' c1 c2 md = Some fmd ->
      forall v1 v2,
        sameValuationExcept v1 v2 md ->
        forall v1' c' l,
          step0 (v1, c) l (v1', c') ->
          forall c1',
            plug C c' c1' ->
            exists vc2' : valuation * cmd,
              cstep (v2, c2) l vc2' /\
              (exists nmd,
                  validator' c1' (snd vc2') nmd = Some fmd /\
                  sameValuationExcept v1' (fst vc2') nmd).
Proof.
Admitted.

(* 20 points *)
Lemma validator_ok':
  forall md s t,
    (match validator' s t md with
     | Some _ => True
     | None => False
     end)->
    forall sv tv,
      sameValuationExcept sv tv md ->
      (sv, s) =| (tv, t).
Proof.
  (* apply simulation *)
Admitted.

(* 5 points *)
Theorem validator_ok:
  forall v s t, validator s t = true -> (v, s) =| (v, t).
Proof.
Admitted.