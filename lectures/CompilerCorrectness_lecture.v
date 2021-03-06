(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 9: Compiler Correctness
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

Set Implicit Arguments.


(* Let's look at another example of what we can model with operational
 * semantics: correctness of compiler transformations.  Our inspiration here is
 * the seminal project CompCert, which uses Coq to verify a realistic C
 * compiler.  We will adopt the same *simulation*-based techniques as CompCert,
 * albeit on a simpler language and with simpler compiler phases.  We'll stick
 * to transformations from the source language to itself, since that's enough to
 * illustrate the big ideas.  Here's the object language that we'll use, which
 * is _almost_ the same as from the operational semantics lecture. *)

Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| If (e : arith) (then_ else_ : cmd)
| While (e : arith) (body : cmd)
| Output (e : arith).
(* The last constructor above is the new one, for generating an _output_ value,
 * say to display in a terminal.  By including this operation, we create
 * interesting differences between the behaviors of different nonterminating
 * programs.  A correct compiler should preserve these differences. *)

(* The next span of notations and definitions is the same as from operational
   semantics lecture. *)

Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
(*Declare Scope arith_scope.*)
Infix "+" := Plus : arith_scope.
Infix "-" := Minus : arith_scope.
Infix "*" := Times : arith_scope.
Delimit Scope arith_scope with arith.
Notation "x <- e" := (Assign x e%arith) (at level 75).
Infix ";;" := Sequence (at level 76). (* This one changed slightly, to avoid parsing clashes. *)
Notation "'when' e 'then' then_ 'else' else_ 'done'" := (If e%arith then_ else_) (at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" := (While e%arith body) (at level 75).

Definition valuation := fmap var nat.
Fixpoint interp (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
    match v $? x with
    | None => 0
    | Some n => n
    end
  | Plus e1 e2 => interp e1 v + interp e2 v
  | Minus e1 e2 => interp e1 v - interp e2 v
  | Times e1 e2 => interp e1 v * interp e2 v
  end.

Inductive context :=
| Hole
| CSeq (C : context) (c : cmd).

Inductive plug : context -> cmd -> cmd -> Prop :=
| PlugHole : forall c, plug Hole c c
| PlugSeq : forall c C c' c2,
  plug C c c'
  -> plug (CSeq C c2) c (Sequence c' c2).

(* Here's our first difference.  We add a new parameter to [step0], giving a
 * _label_ that records which _externally visible effect_ the step has.  For
 * this language, output is the only externally visible effect, so a label
 * records an optional output value.  Including this element makes our semantics
 * a _labelled transition system_. *)

Inductive step0 : valuation * cmd -> option nat -> valuation * cmd -> Prop :=
| Step0Assign : forall v x e,
  step0 (v, Assign x e) None (v $+ (x, interp e v), Skip)
| Step0Seq : forall v c2,
  step0 (v, Sequence Skip c2) None (v, c2)
| Step0IfTrue : forall v e then_ else_,
  interp e v <> 0
  -> step0 (v, If e then_ else_) None (v, then_)
| Step0IfFalse : forall v e then_ else_,
  interp e v = 0
  -> step0 (v, If e then_ else_) None (v, else_)
| Step0WhileTrue : forall v e body,
  interp e v <> 0
  -> step0 (v, While e body) None (v, Sequence body (While e body))
| Step0WhileFalse : forall v e body,
  interp e v = 0
  -> step0 (v, While e body) None (v, Skip)
| Step0Output : forall n v e,
  interp e v = n ->
  step0 (v, Output e) (Some n) (v, Skip).

(* It's easy to push labels through steps with context. *)
Inductive cstep : valuation * cmd -> option nat -> valuation * cmd -> Prop :=
| CStep : forall C v c l v' c' c1 c2,
  plug C c c1
  -> step0 (v, c) l (v', c')
  -> plug C c' c2
  -> cstep (v, c1) l (v', c2).

(* To characterize correct compilation, it is helpful to define a relation to
 * capture which output _traces_ a command might generate.  Note that, for us, a
 * trace is a list of output values and/or terminating markers.  We drop silent
 * labels as we run, and we use [Some n] for outputting of [n] and [None] for
 * termination. *)
Inductive generate : valuation * cmd -> list (option nat) -> Prop :=
| GenDone : forall vc,
  generate vc [] (* truncate *)
| GenSkip : forall v,
  generate (v, Skip) [None] (* termination *)
| GenSilent : forall vc vc' ns,
  cstep vc None vc'
  -> generate vc' ns
  -> generate vc ns
| GenOutput : forall vc n vc' ns,
  cstep vc (Some n) vc'
  -> generate vc' ns
  -> generate vc (Some n :: ns).

Hint Constructors plug step0 cstep generate : core.

(* Notice that [generate] is defined so that, for any two of a starting state's
 * traces, one is a prefix of the other.  The same wouldn't necessarily hold if
 * our language were nondeterministic. *)

(* We define trace inclusion to capture the notion of
 * _preserving all behaviors_. *)
Definition traceInclusion (vc1 vc2 : valuation * cmd) :=
  forall ns, generate vc1 ns -> generate vc2 ns.
Infix "<|" := traceInclusion (at level 70).

(* And trace equivalence captures _having the same behaviors_. *)
Definition traceEquivalence (vc1 vc2 : valuation * cmd) :=
  vc1 <| vc2 /\ vc2 <| vc1.
Infix "=|" := traceEquivalence (at level 70).

(* Trace equivalence is an appropriate notion of correctness, to relate the
 * "before" and "after" programs of a compiler transformation.  

 * Note that here we break from our usual modus operandi, as we will not be 
 * using invariants to characterize correctness!  This kind of trace 
 * equivalence is one of the other big concepts that competes with 
 * invariants to unify different correctness notions. *)

(* Here's a simple example program, which outputs how many days have elapsed at
 * the end of each one-month period (with a simplified notion of "month"!). *)

Definition daysPerWeek := 7.
Definition weeksPerMonth := 4.
Definition daysPerMonth := (daysPerWeek * weeksPerMonth)%arith.
Print daysPerMonth.
(* We are purposely building an expression with arithmetic that can be resolved
 * at compile time, to give our optimizations something to do. *)

Example month_boundaries_in_days :=
  "acc" <- 0;;
  while 1 loop
    when daysPerMonth then
      "acc" <- "acc" + daysPerMonth;;
      Output "acc"
    else
      (* Oh no!  We must have calculated it wrong, since we got zero! *)
      (* And, yes, we know this spot can never be reached.  Some of our
       * optimizations will prove it for us! *)
      Skip
    done
  done.

(* Moderately laboriously, we can prove a particular example trace for this
 * program, including its first two outputs.  Traces of all lengths exist,
 * because the program does not terminate, generating new output infinitely
 * often. *)

Hint Extern 1 (interp _ _ = _) => simplify; equality : core.
Hint Extern 1 (interp _ _ <> _) => simplify; equality : core.

Theorem first_few_values :
  generate ($0, month_boundaries_in_days) [Some 28; Some 56].
Proof.
  unfold month_boundaries_in_days.
  Print generate.
  eapply GenSilent.
  eapply CStep with (C := CSeq Hole _); eauto.
  eapply GenSilent.
  eapply CStep with (C := Hole); eauto.
  eapply GenSilent.
  eapply CStep with (C := Hole); eauto.
  eapply GenSilent.
  eapply CStep with (C := CSeq Hole _); eauto.
  eapply GenSilent.
  eapply CStep with (C := CSeq (CSeq Hole _) _); eauto.
  simplify.
  eapply GenSilent.
  eapply CStep with (C := CSeq Hole _); eauto.
  eapply GenOutput.
  eapply CStep with (C := CSeq Hole _); eauto.
  eapply GenSilent.
  eapply CStep with (C := Hole); eauto.
  eapply GenSilent.
  eapply CStep with (C := Hole); eauto.
  eapply GenSilent.
  eapply CStep with (C := CSeq Hole _); eauto.
  eapply GenSilent.
  eapply CStep with (C := CSeq (CSeq Hole _) _); eauto.
  simplify.
  eapply GenSilent.
  eapply CStep with (C := CSeq Hole _); eauto.
  eapply GenOutput.
  eapply CStep with (C := CSeq Hole _); eauto.
  Check GenDone.
  eapply GenDone.
Qed.


(** * Basic Simulation Arguments and Optimizing Expressions *)

(* Let's define an optimization that just simplifies expressions. *)

Fixpoint cfoldArith (e : arith) : arith :=
  match e with
  | Const _ => e
  | Var _ => e
  | Plus e1 e2 =>
    let e1' := cfoldArith e1 in
    let e2' := cfoldArith e2 in
    match e1', e2' with
    | Const n1, Const n2 => Const (n1 + n2)
    | _, _ => Plus e1' e2'
    end
  | Minus e1 e2 =>
    let e1' := cfoldArith e1 in
    let e2' := cfoldArith e2 in
    match e1', e2' with
    | Const n1, Const n2 => Const (n1 - n2)
    | _, _ => Minus e1' e2'
    end
  | Times e1 e2 =>
    let e1' := cfoldArith e1 in
    let e2' := cfoldArith e2 in
    match e1', e2' with
    | Const n1, Const n2 => Const (n1 * n2)
    | _, _ => Times e1' e2'
    end
  end.

Theorem cfoldArith_ok : forall v e,
    interp (cfoldArith e) v = interp e v.
Proof.
  induct e; simplify; try equality.
  all: cases (cfoldArith e1); simplify; try equality.
  all: cases (cfoldArith e2); simplify; try equality.
Qed.

Fixpoint cfoldExprs (c : cmd) : cmd :=
  match c with
  | Skip => c
  | Assign x e => Assign x (cfoldArith e)
  | Sequence c1 c2 => Sequence (cfoldExprs c1) (cfoldExprs c2)
  | If e then_ else_ => If (cfoldArith e) (cfoldExprs then_) (cfoldExprs else_)
  | While e body => While (cfoldArith e) (cfoldExprs body)
  | Output e => Output (cfoldArith e)
  end.

(* Here's what our optimization does to the example program. *)
Print month_boundaries_in_days.
Compute cfoldExprs month_boundaries_in_days.

(* It's actually not obvious how to prove trace equivalence for this kind of
 * optimization, and we should be on the lookout for general principles that
 * help us avoid rehashing the same argument structure for each optimization.
 * To let us prove such principles, we first establish a few key properties of
 * the object language. *)

(* First, any program that isn't a [Skip] can make progress. *)
Theorem skip_or_step : forall v c,
    c = Skip
    \/ exists v' l c', cstep (v, c) l (v', c').
Proof.
  induct c; simplify; first_order; subst;
    try match goal with
        | [ H : cstep _ _ _ |- _ ] => invert H
        end;
    try match goal with
        | [ |- context[cstep (?v, If ?e _ _)] ] => cases (interp e v ==n 0)
        | [ |- context[cstep (?v, While ?e _)] ] => cases (interp e v ==n 0)
        end; eauto 10.
Qed.

(* Now, a set of (boring) lemmas relevant to contexts:

   Skipping.... 
 *)

Theorem plug_function : forall C c1 c2, plug C c1 c2
  -> forall c2', plug C c1 c2'
  -> c2 = c2'.
Proof.
  induct 1; invert 1; eauto.
  apply IHplug in H5.
  equality.
Qed.

Lemma peel_cseq : forall C1 C2 c (c1 c2 : cmd),
    C1 = C2 /\ c1 = c2
    -> CSeq C1 c = CSeq C2 c /\ c1 = c2.
Proof.
  equality.
Qed.

Hint Resolve peel_cseq : core.

Lemma plug_deterministic : 
     forall v C c1 c2, plug C c1 c2
  -> forall l vc1, step0 (v, c1) l vc1
  -> forall C' c1', plug C' c1' c2
  -> forall l' vc1', step0 (v, c1') l' vc1'
  -> C' = C /\ c1' = c1.
Proof.
  induct 1; invert 1; invert 1; invert 1; auto;
    try match goal with
        | [ H : plug _ _ _ |- _ ] => invert1 H
        end; eauto.
Qed.

 
(* If you want more details, see skipped portions from 
 * [OperationalSemantics.v], though the details are not important here *)

(* Finally, the big theorem we are after: the [cstep] relation is
 * deterministic. 
 *)

Lemma deterministic0 : forall vc l vc',
  step0 vc l vc'
  -> forall l' vc'', step0 vc l' vc''
                     -> l = l' /\ vc'' = vc'.
Proof.
  invert 1; invert 1; simplify; propositional.
Qed.

Theorem deterministic : forall vc l vc',
  cstep vc l vc'
  -> forall l' vc'', cstep vc l' vc''
                     -> l = l' /\ vc' = vc''.
Proof.
  invert 1; invert 1; simplify.
  eapply plug_deterministic in H0; eauto.
  invert H0.
  match goal with
  | [ H : step0 _ _ _, H' : step0 _ _ _ |- _ ] => eapply deterministic0 in H; [ | apply H' ]
  end.
  propositional; subst; auto.
  invert H0.
  auto.
  eapply plug_function in H2; eauto.
  equality.
Qed.

(* OK, we are ready for the first variant of today's big proof technique,
 * _simulation_.  The method is much like with invariants.  Recall that, in our
 * old workhorse technique, we pick a predicate over states, and we show that
 * all steps preserve it.  Simulation is very similar, but now we have a
 * two-argument predicate or _relation_ between states of two systems.  The
 * relation is a simulation when it is able to track execution in one system by
 * playing appropriate steps in the other.  For deterministic systems like ours,
 * the existence of a simulation implies trace equivalence. *)
Section simulation.
  (* Here's the kind of relation we assume. *)
  Variable R : valuation * cmd -> valuation * cmd -> Prop.

  (* Starting from two related states, when the lefthand one makes a step, the
   * righthand one can make a matching step, such that the new states are also
   * related. *)
  Hypothesis one_step : forall vc1 vc2, 
      R vc1 vc2
    -> forall vc1' l, cstep vc1 l vc1'
    -> exists vc2', cstep vc2 l vc2' /\ R vc1' vc2'.

  (* When a righthand command is related to [Skip], it must be [Skip], too. *)
  Hypothesis agree_on_termination : forall v1 v2 c2, 
    R (v1, Skip) (v2, c2) -> c2 = Skip.

  (* First (easy) step: [R] implies left-to-right trace inclusion. *)

  Lemma simulation_fwd' : 
       forall vc1 ns, generate vc1 ns
    -> forall vc2, R vc1 vc2
    -> generate vc2 ns.
  Proof.
    induct 1; simplify; eauto.

    cases vc2.
    apply agree_on_termination in H; subst.
    info_auto.

    (* See [H] and [H1] 
      
      vc------R------>vc2
       |
       |None
       |
       v
      vc'
      
    *)
    eapply one_step in H1.
    first_order.
    eapply GenSilent.
    eassumption.
    eapply IHgenerate.
    eassumption.
    eassumption.

    (* See [H] and [H1] 
      
      vc------R------>vc2
       |
       |Some(n)
       |
       v
      vc'
      
    *)
    eapply one_step in H1.
    first_order.
    eapply GenOutput.
    eassumption.
    apply IHgenerate.
    eassumption.
    eassumption.
  Qed.

  Theorem simulation_fwd : forall vc1 vc2, R vc1 vc2
    -> vc1 <| vc2.
  Proof.
    unfold traceInclusion.
    simplify.
    eapply simulation_fwd'.
    eassumption.
    eassumption.
  Restart.
    unfold traceInclusion; eauto using simulation_fwd'.
  Qed.

  (* Second (slightly harder) step: [R] implies right-to-left 
   * trace inclusion. *)

  Lemma simulation_bwd' : 
       forall vc2 ns, generate vc2 ns
    -> forall vc1, R vc1 vc2
    -> generate vc1 ns.
  Proof.
    induct 1; simplify; eauto.

    cases vc1.
    assert (c = Skip \/ exists v' l c', 
       cstep (v0, c) l (v', c')) by apply skip_or_step.
    first_order; subst.
    info_auto.
    (* See [H0] and [H] 
      
      (v0,c)------R------>(v,Skip)
        |
        |x0
        |
        v
      (x,x1)
      
     *)
    eapply one_step in H; eauto.
    first_order.
      (* [cstep (v, Skip) x0 vc2'] derives a contradiction *)
    invert H.
    invert H4.
    invert H5.
    
    (* See [H1] and [H] 
      
      vc1------R------>vc
                       |
                       |None
                       |
                       v
                      vc'
      
    *)
    cases vc1; cases vc.
    (* See [H] and [H1]
      
      (v,c)------R------>(v0,c0)
                            |
                            |None
                            |
                            v
                           vc'
      
    *)
    assert (c = Skip \/ exists v' l c', 
      cstep (v, c) l (v', c')) by apply skip_or_step.
    first_order; subst.
    apply agree_on_termination in H1; subst.
      (* [cstep (v0, Skip) None vc'] derives a contradiction *)
    invert H.
    invert H3.
    invert H4.
    (* See [H], [H1] and [H2]
      
      (v,c)------R------>(v0,c0)
        |                   |
        |x0                 |None
        |                   |
        v                   v
      (x,x1)               vc' 
      
    *)
    specialize (one_step H1 H2).
    first_order.
      (* The cstep in [H] and [H3] must represent the same 
         label and end state thanks to determinism. *)
    eapply deterministic in H; eauto.
    propositional; subst.
    eapply GenSilent.
    eassumption.
    apply IHgenerate.
    trivial.

    cases vc1; cases vc.
    (* See [H] and [H1]
      
      (v,c)------R------>(v0,c0)
                            |
                            |Some n
                            |
                            v
                           vc'
      
    *)
    assert (c = Skip \/ exists v' l c', 
      cstep (v, c) l (v', c')) by apply skip_or_step.
    first_order; subst.
    apply agree_on_termination in H1; subst.
    invert H.
    invert H3.
    invert H4.
    (* See [H], [H1] and [H2]
      
      (v,c)------R------>(v0,c0)
        |                   |
        |x0                 |Some n
        |                   |
        v                   v
      (x,x1)               vc' 
      
    *)
    specialize (one_step H1 H2).
    first_order.
      (* The cstep in [H] and [H3] must represent the same 
         label and end state thanks to determinism. *)
    eapply deterministic in H; eauto.
    propositional; subst.
    info_eauto.
  Qed.

  Theorem simulation_bwd : forall vc1 vc2, R vc1 vc2
    -> vc2 <| vc1.
  Proof.
    unfold traceInclusion; eauto using simulation_bwd'.
  Qed.

  (* Put them together and we have trace equivalence. *)

  Theorem simulation : forall vc1 vc2, R vc1 vc2
    -> vc1 =| vc2.
  Proof.
    simplify. 
    unfold traceEquivalence. split. 
    auto using simulation_fwd. 
    auto using simulation_bwd.
  Qed.
End simulation.

(* Now to prove our particular optimization.  First, original steps can be
 * lifted into optimized steps. *)

Lemma cfoldExprs_ok' : forall v1 c1 l v2 c2,
    step0 (v1, c1) l (v2, c2)
    -> step0 (v1, cfoldExprs c1) l (v2, cfoldExprs c2).
Proof.
  invert 1; simplify;
    try match goal with
        | [ _ : context[interp ?e ?v] |- _ ] => 
          rewrite <- (cfoldArith_ok v e) in *
        | [ |- context[interp ?e ?v] ] => 
          rewrite <- (cfoldArith_ok v e)
        end; eauto.
Qed.

(* It helps to add optimization on contexts, as a proof device. *)
Fixpoint cfoldExprsContext (C : context) : context :=
  match C with
  | Hole => Hole
  | CSeq C c => CSeq (cfoldExprsContext C) (cfoldExprs c)
  end.

(* The optimization can be applied over [plug]. *)
Lemma plug_cfoldExprs1 : forall C c1 c2, plug C c1 c2
  -> plug (cfoldExprsContext C) (cfoldExprs c1) (cfoldExprs c2).
Proof.
  induct 1; simplify; eauto.
Qed.

Hint Resolve plug_cfoldExprs1 : core.

(* The main correctness property! *)
Theorem cfoldExprs_ok : forall v c,
    (v, c) =| (v, cfoldExprs c).
Proof.
  simplify.
  (* Notice our clever choice of a simulation relation here, much as we often
   * choose strengthened invariants.  We basically just recast the theorem
   * statement as a two-state predicate using equality. *)
  apply simulation with 
    (R := fun vc1 vc2 => fst vc1 = fst vc2
                         /\ snd vc2 = cfoldExprs (snd vc1)).
    (* The three sub-goals correspond to the 2 hypotheses and 1 variable *)
    
  2: { simplify. propositional. } (* agree_on_termination *)
  2: { simplify. propositional. } (* R *)
  simplify. propositional. (* one_step *)
    
  invert H0; simplify; subst.
  apply cfoldExprs_ok' in H3.
  eexists; propositional.
  cases vc2. simplify. subst. (* [H2] *)
  info_eauto.
  simplify. trivial.
  equality.
Qed.
















































































(** * Simulations That Allow Skipping Steps *)

(* Here's a reasonable variant of the last optimization: when an [If] test
 * expression reduces to a constant, replace the [If] with whichever branch is
 * guaranteed to run. *)
Fixpoint cfold (c : cmd) : cmd :=
  match c with
  | Skip => c
  | Assign x e => Assign x (cfoldArith e)
  | Sequence c1 c2 => Sequence (cfold c1) (cfold c2)
  | If e then_ else_ =>
    let e' := cfoldArith e in
    match e' with
    | Const n => if n ==n 0 then cfold else_ else cfold then_
    | _ => If e' (cfold then_) (cfold else_)
    end
  | While e body => While (cfoldArith e) (cfold body)
  | Output e => Output (cfoldArith e)
  end.

(* Here's how our running example optimizes further. *)
Print month_boundaries_in_days.

Compute cfold month_boundaries_in_days.

(* It will be helpful to have a shorthand for steps that don't generate output.
 * [Notation] is a useful way to introduce a shorthand so that it looks exactly
 * the same as its expansion, to all Coq tactics. *)
Notation silent_cstep := (fun a b => cstep a None b).


(* Silent steps have a few interesting properties, proved here. *)

Lemma silent_generate_fwd : forall ns vc vc',
    silent_cstep^* vc vc'
    -> generate vc ns
    -> generate vc' ns.
Proof.
  induct 1; simplify; eauto.
  invert H1; auto.

  invert H.
  invert H3.
  invert H4.

  eapply deterministic in H; eauto.
  propositional; subst.
  auto.

  eapply deterministic in H; eauto.
  equality. (* derive contradiction *)
Qed.

Lemma silent_generate_bwd : forall ns vc vc',
    silent_cstep^* vc vc'
    -> generate vc' ns
    -> generate vc ns.
Proof.
  induct 1. 
  equality. 
  simplify. eapply GenSilent. eassumption. equality.
Qed.

Lemma generate_Skip : forall v a ns,
    generate (v, Skip) (Some a :: ns)
    -> False.
Proof.
  (* Skipping this.. *)
  induct 1; simplify.

  invert H.
  invert H3.
  invert H4.

  invert H.
  invert H3.
  invert H4.
Qed.

Hint Resolve silent_generate_fwd silent_generate_bwd generate_Skip : core.

(* You might have noticed that our old notion of simulation 
 * doesn't apply to the new optimization.  The reason is that, 
 * because the optimized program skips some steps, some steps 
 * in the source program may not have matching steps in the 
 * optimized program.  Let's extend simulation to allow skipped 
 * steps. *)
Section simulation_skipping.
  (* Now the relation takes a number as an argument.  The 
   * idea is that, for [R n vc1 vc2], at most [n] steps of 
   * [vc1] may go unmatched by [vc2], before we finally find 
   * one that matches.  It is an interesting exercise to work
   * out why, without tracking such quantities, this notion of 
   * simulation wouldn't imply trace equivalence! *)
  Variable R : nat -> valuation * cmd -> valuation * cmd -> Prop.

  (* Now this key hypothesis has two cases. *)
  Hypothesis one_step : 
       forall n vc1 vc2, R n vc1 vc2
    -> forall vc1' l, cstep vc1 l vc1'
    
         (* Case 1: Skipping a (silent!) step, decreasing [n] *)
      -> (exists n', n = S n' /\ l = None /\ R n' vc1' vc2)

         (* Case 2: Matching the step like before; note how [n]
          * resets to an arbitrary new limit! *)
         \/ exists n' vc2', cstep vc2 l vc2' /\ R n' vc1' vc2'.

  Hypothesis agree_on_termination : forall n v1 v2 c2, 
    R n (v1, Skip) (v2, c2) -> c2 = Skip.

  (* The forward direction is just as easy to prove. *)

  Lemma simulation_skipping_fwd' : 
       forall vc1 ns, generate vc1 ns
    -> forall n vc2, R n vc1 vc2
    -> generate vc2 ns.
  Proof.
    induct 1; simplify; eauto.

    cases vc2.
    apply agree_on_termination in H.
    subst.
    auto.

    (* See [H] and [H1] 
      
      vc------Rn------>vc2
       |
       |None
       |
       v
      vc'
      
      [H0] : generate vc' ns
    *)
    eapply one_step in H; eauto.
    first_order.
    eapply GenSilent.
    eassumption.
    eapply IHgenerate.
    eassumption.

    eapply one_step in H1; eauto.
    first_order.
    equality.
    eapply GenOutput.
    eassumption.
    eapply IHgenerate.
    eassumption.
  Qed.

  Theorem simulation_skipping_fwd : forall n vc1 vc2, R n vc1 vc2
    -> vc1 <| vc2.
  Proof.
    unfold traceInclusion; eauto using simulation_skipping_fwd'.
  Qed.

  (* Right to left isn't so obvious: 
   *    a step on the right can now be matched by 
   *    _one or more_ steps on the left, preserving [R]. *)
  Lemma match_step : forall n vc2 l vc2' vc1,
      cstep vc2 l vc2'
      -> R n vc1 vc2
      -> exists vc1' vc1'' n', silent_cstep^* vc1 vc1'
                              /\ cstep vc1' l vc1''
                              /\ R n' vc1'' vc2'.
  Proof.
    induct n; simplify.

    cases vc1; cases vc2.
    assert (c = Skip \/ exists v' l' c', 
      cstep (v, c) l' (v', c')) by apply skip_or_step.
    first_order; subst.
    apply agree_on_termination in H0; subst.
    invert H.
    invert H2.
    invert H3.
    (* See [H], [H0] and [H1] 
      
      (v,c)------R(0)------>(v0,c0)
        |                      |
        |x0                    |l
        |                      |
        v                      v
      (x,x1)                  vc2'
      
    *)
    1: { eapply one_step in H0; eauto.
    first_order.
    equality. (* derive contradiction from [H0] *)
    eapply deterministic in H; eauto.
    first_order; subst.
    do 3 eexists. propositional.
    eapply TrcRefl.
    eassumption.
    eassumption.
    }
    
    cases vc1; cases vc2.
    assert (c = Skip \/ exists v' l' c', 
      cstep (v, c) l' (v', c')) by apply skip_or_step.
    first_order; subst.
    apply agree_on_termination in H0; subst.
    invert H.
    invert H2.
    invert H3.
    (* See [H], [H0] and [H1] 
      
      (v,c)------R(n+1)---->(v0,c0)
        |                      |
        |x0                    |l
        |                      |
        v                      v
      (x,x1)                  vc2'
      
    *)
    
    (* Skipping.. rest similar to earlier part of the 
       proof *)
    eapply one_step in H0; eauto.
    first_order; subst.
    invert H0.
    eapply IHn in H3; eauto.
    first_order.
    info_eauto 8.
    eapply deterministic in H; eauto.
    first_order; subst.
    eauto 6.
  Qed.

  Lemma step_to_termination : forall vc v,
      silent_cstep^* vc (v, Skip)
      -> generate vc [None].
  Proof.
    clear.
    induct 1.
    constructor.
    eapply GenSilent.
    eassumption.
    eassumption.
  Restart.
    induct 1; eauto.
  Qed.

  Hint Resolve step_to_termination : core.

  Lemma R_Skip : forall n vc1 v,
      R n vc1 (v, Skip)
      -> exists v', silent_cstep^* vc1 (v', Skip).
  Proof.
    induct n; simplify.

    cases vc1.
    assert (c = Skip \/ exists v' l c', cstep (v0, c) l (v', c')) by apply skip_or_step.
    first_order; subst.
    eexists.
    eapply TrcRefl.

    (* See [H] and [H0]
      
      (v0,c)------R(0)------>(v,Skip)
        |
        |x0
        |
        v
      (x,x1)
      
    *)
    eapply one_step in H; eauto.
    first_order.
    equality.
    invert H.
    invert H4.
    invert H5.

    cases vc1.
    assert (c = Skip \/ exists v' l c', cstep (v0, c) l (v', c')) by apply skip_or_step.
    first_order; subst.
    info_eauto.
    (* See [H] and [H0]
      
      (v0,c)------R(n+1)------>(v,Skip)
        |
        |x0
        |
        v
      (x,x1)
      
    *)
    eapply one_step in H; eauto.
    clear one_step.
    first_order; subst.
    invert H.
    apply IHn in H2.
    first_order.
    eexists.
    eapply TrcFront.
    eassumption.
    eassumption.
    invert H.
    invert H4.
    invert H5.
  Qed.

  Lemma simulation_skipping_bwd' : forall ns vc2, generate vc2 ns
    -> forall n vc1, R n vc1 vc2
      -> generate vc1 ns.
  Proof.
    induct 1; simplify; eauto.

    cases vc1.
    Check R_Skip.
    apply R_Skip in H; first_order.
    Check step_to_termination.
    eapply step_to_termination.
    eassumption.

    (* See [H], [H0] and [H1] 
       
       vc1---R(n)--->vc
                      |
                      |None
                      |
                      v
                     vc'
     
     H0: generate vc' ns
     
     To Show: generate vc1 ns
    *)
    eapply match_step in H1; eauto.
    first_order.
    clear one_step; clear agree_on_termination.

    (* See [H], [H0], [H1], [H2], [H3]
       
       vc1---R(n)---->vc
        |             |
        |None*        |None
        |             |
        v             |
        x             |
        |             |
        |None         |
        |             |
        v             v
        x0---R(x1)--->vc'
     
     H0: generate vc' ns
     
     To Show: generate vc1 ns
    *)
    Check silent_generate_bwd.
    eapply silent_generate_bwd.
    eassumption.
    (* See [H], [H0], [H1], [H2], [H3]
       
       vc1---R(n)---->vc
        |             |
        |None*        |None
        |             |
        v             |
        x             |
        |             |
        |None         |
        |             |
        v             v
        x0---R(x1)--->vc'
     
     H0: generate vc' ns
     
     To Show: generate x ns
    *)
    eapply GenSilent.
    eassumption.
    (* See [H], [H0], [H1], [H2], [H3]
       
       vc1---R(n)---->vc
        |             |
        |None*        |None
        |             |
        v             |
        x             |
        |             |
        |None         |
        |             |
        v             v
        x0---R(x1)--->vc'
     
     H0: generate vc' ns
     
     To Show: generate x0 ns
    *)
    eapply IHgenerate.
    eassumption.

    (* See [H], [H0] and [H1] 
       
       vc1---R(n0)--->vc
                      |
                      |Some(n)
                      |
                      v
                     vc'
     
     H0: generate vc' ns
     
     To Show: generate vc1 ns
    *)
    eapply match_step in H1; eauto.
    first_order.
    clear one_step; clear agree_on_termination.

    (* See [H], [H0], [H1], [H2], [H3]
       
       vc1---R(n)---->vc
        |             |
        |None*        |Some(n)
        |             |
        v             |
        x             |
        |             |
        |Some(n)      |
        |             |
        v             v
        x0---R(x1)--->vc'
     
     H0: generate vc' ns
     
     To Show: generate vc1 (Some n::ns)
    *)
    eapply silent_generate_bwd.
    eassumption.
    (* See [H], [H0], [H1], [H2], [H3]
       
       vc1---R(n)---->vc
        |             |
        |None*        |Some(n)
        |             |
        v             |
        x             |
        |             |
        |Some(n)      |
        |             |
        v             v
        x0---R(x1)--->vc'
     
     H0: generate vc' ns
     
     To Show: generate x (Some n::ns)
    *)
    eapply GenOutput.
    eassumption.
    eapply IHgenerate.
    eassumption.
  Qed.

  Theorem simulation_skipping_bwd : forall n vc1 vc2, R n vc1 vc2
    -> vc2 <| vc1.
  Proof.
    unfold traceInclusion; eauto using simulation_skipping_bwd'.
  Qed.

  Theorem simulation_skipping : forall n vc1 vc2, R n vc1 vc2
    -> vc1 =| vc2.
  Proof.
    simplify; split; eauto using simulation_skipping_fwd, simulation_skipping_bwd.
  Qed.
End simulation_skipping.

Hint Extern 1 (_ < _) => linear_arithmetic : core.
Hint Extern 1 (_ >= _) => linear_arithmetic : core.
Hint Extern 1 (_ <> _) => linear_arithmetic : core.

(* We will need to do some book keeping of [n] values.  This function is the
 * trick, as we only need to skip steps based on removing [If]s from the code.
 * That means the number of [If]s in a program is an upper bound on skipped
 * steps.  (It's not a tight bound, because some [If]s may be in branches that
 * are themselves removed by the optimization!) *)
Fixpoint countIfs (c : cmd) : nat :=
  match c with
  | Skip => 0
  | Assign _ _ => 0
  | Sequence c1 c2 => countIfs c1 + countIfs c2
  | If _ c1 c2 => 1 + countIfs c1 + countIfs c2
  | While _ c1 => countIfs c1
  | Output _ => 0
  end.


Lemma cfold_ok'' : forall v1 c1 l v2 c2,
    step0 (v1, c1) l (v2, c2)
    -> step0 (v1, cfold c1) l (v2, cfold c2).
Proof.
Abort.

Compute cfold (when 1%arith then 
                 when "x" then Skip else Skip done
               else Skip done).

(* Our notion of [step0] porting must now allow some skipped steps, also showing
 * that they decrease [If] count. *)
Lemma cfold_ok' : forall v1 c1 l v2 c2,
    step0 (v1, c1) l (v2, c2)
    -> step0 (v1, cfold c1) l (v2, cfold c2)
       \/ (l = None /\ v1 = v2 /\ cfold c1 = cfold c2 /\ countIfs c2 < countIfs c1).
Proof.
  invert 1; simplify;
    try match goal with
        | [ _ : context[interp ?e ?v] |- _ ] => 
          rewrite <- (cfoldArith_ok v e) in *
        | [ |- context[interp ?e ?v] ] => 
          rewrite <- (cfoldArith_ok v e)
        end;
    repeat match goal with
           | [ |- context[match ?E with _ => _ end] ] => 
             cases E; subst; simplify
           end; propositional; eauto.
Qed.

(* Now some fiddling with contexts: *)

(* [cfold] can be applied over contexts. Skipping.. *)
Fixpoint cfoldContext (C : context) : context :=
  match C with
  | Hole => Hole
  | CSeq C c => CSeq (cfoldContext C) (cfold c)
  end.

(* Relate plugging a context with [cfold] and [cfoldContext] *)
Lemma plug_cfold1 : forall C c1 c2, plug C c1 c2
  -> plug (cfoldContext C) (cfold c1) (cfold c2).
Proof.
  induct 1; simplify; eauto.
Qed.

Hint Resolve plug_cfold1 : core.

(* If two expressions are the same if [cfold]ed, 
   then plugging them in the same context and 
   folding them would produce the same expressions *)
Lemma plug_samefold : forall C c1 c1',
    plug C c1 c1'
    -> forall c2 c2', plug C c2 c2'
    -> cfold c1 = cfold c2
    -> cfold c1' = cfold c2'.
Proof.
  induct 1; invert 1; simplify; propositional.
  f_equal; eauto.
Qed.

Hint Resolve plug_samefold : core.

(* Lifting [countIfs] to plug *)
Lemma plug_countIfs : forall C c1 c1',
    plug C c1 c1'
    -> forall c2 c2', plug C c2 c2'
    -> countIfs c1 < countIfs c2
    -> countIfs c1' < countIfs c2'.
Proof.
  induct 1; invert 1; simplify; propositional.
  apply IHplug in H5; linear_arithmetic.
Qed.

Hint Resolve plug_countIfs : core.

Hint Extern 1 (interp ?e _ = _) =>
  match goal with
  | [ H : cfoldArith e = _ |- _ ] => rewrite <- cfoldArith_ok; rewrite H
  end : core.
Hint Extern 1 (interp ?e _ <> _) =>
  match goal with
  | [ H : cfoldArith e = _ |- _ ] => rewrite <- cfoldArith_ok; rewrite H
  end : core.

(* The final proof is fairly straightforward now. *)
Lemma cfold_ok : forall v c,
    (v, c) =| (v, cfold c).
Proof.
  simplify.
  (* Note the use of [countIfs] in the simulation relation. *)
  apply simulation_skipping with 
    (n := S (countIfs c))
    (R := fun n vc1 vc2 => fst vc1 = fst vc2
                           /\ snd vc2 = cfold (snd vc1)
                           /\ countIfs (snd vc1) < n);
    simplify; propositional; auto.

  (* Skipping rest of the proof as it is straight-forward *)
  invert H0; simplify; subst.
  apply cfold_ok' in H4.
  propositional; subst.
  cases vc2; simplify; subst.
  eauto 11.
  cases vc2; simplify; subst.
  cases n; try linear_arithmetic.
  assert (countIfs c2 < n).
  eapply plug_countIfs in H2; eauto.
  eauto.
  eauto 10.
Qed.