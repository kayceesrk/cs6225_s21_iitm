(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Supplementary Coq material: unification and logic programming
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/
  * Much of the material comes from CPDT <http://adam.chlipala.net/cpdt/> by the same author. *)

Require Import Frap.

Set Implicit Arguments.

(** * Introducing Logic Programming *)

(* Recall the definition of addition from the standard library. *)

Definition real_plus := Eval compute in plus.
Print real_plus.

(* Recursive definition :: FP style. *)

(* Inductive relations :: Logic style. *)
Inductive plusR : nat -> nat -> nat -> Prop :=
| PlusO : forall m, plusR O m m
| PlusS : forall n m r, plusR n m r -> plusR (S n) m (S r).

(* Recall that Coq will automatically derive the induction principle for 
 * inductives. For example: *)
 
Print list.
Check list_ind.

(* Similarly we have a induction principle for plusR. *)

Check plusR_ind.

(* Intuitively, a fact [plusR n m r] only holds when [plus n m = r].  It is not
 * hard to prove this correspondence formally. *)

Theorem plus_plusR : forall n m,
  plusR n m (n + m).
Proof.
  induct n; simplify.

  (* apply PlusO. *)
  (* exact (PlusO m). *)
  constructor.
  (* [constructor] applies the corresponding constructor definition. *)

  constructor.
  apply IHn.
Qed.

(* We see here another instance of the very mechanical proof pattern that came
 * up before: keep trying constructors and hypotheses.  The tactic [auto] will
 * automate searching through sequences of that kind, when we prime it with good
 * suggestions of single proof steps to try, as with this command: *)

Hint Constructors plusR.

(* That is, every constructor of [plusR] should be considered as an atomic proof
 * step, from which we enumerate step sequences. *)

Theorem plus_plusR_snazzy : forall n m,
  plusR n m (n + m).
Proof.
  induct n; simplify; auto.
Qed.

Theorem plusR_plus : forall n m r,
  plusR n m r
  -> r = n + m.
Proof.
  induct 1. 
    (* [induct 1] instructs Coq to perform induction on the first hypothesis 
     of the theorem, which is [plusR n m r]. *) 
  2: {
    (* Choose the second subgoal to prove first *)
    simplify; linear_arithmetic.
  }
  simplify; linear_arithmetic.
Qed.

(* With the functional definition of [plus], simple equalities about arithmetic
 * follow by computation. *)

Example four_plus_three : 4 + 3 = 7.
Proof.
  reflexivity.
Qed.

Print four_plus_three.

(* With the relational definition, the same equalities take more steps to prove,
 * but the process is completely mechanical.  
 
 * For example, consider this
 * simple-minded manual proof search strategy.  The steps prefaced by [Fail] are
 * intended to fail; they're included for explanatory value, to mimic a
 * simple-minded try-everything strategy. *)

Example four_plus_three' : plusR 4 3 7.
Proof.
  Fail apply PlusO.
  apply PlusS.
  Fail apply PlusO.
  apply PlusS.
  Fail apply PlusO.
  apply PlusS.
  Fail apply PlusO.
  apply PlusS.
  apply PlusO.

  (* At this point the proof is completed.  It is no doubt clear that a simple
   * procedure could find all proofs of this kind for us.  We are just exploring
   * all possible proof trees, built from the two candidate steps [apply PlusO]
   * and [apply PlusS].  Thus, [auto] is another great match! *)
Restart.
  debug auto.
Qed.

Print four_plus_three'.

(* Let us try the same approach on a slightly more complex goal. *)

Example five_plus_three : plusR 5 3 8.
Proof.
  auto.

  (* This time, [auto] is not enough to make any progress.  
  
   * Since even a single candidate step may lead to an infinite 
   * space of possible proof trees, [auto] is parameterized on the 
   * maximum depth of trees to consider.  
   
   * The default depth is 5, and it turns out that we need depth 6 to prove the
   * goal. *)

  auto 6.
  (* Sometimes it is useful to see a description of the proof tree that [auto]
   * finds, with the [info_auto] variant. *)

Restart.
  info_auto 6.
Restart.
  debug auto 6.
  (* Also shows failed steps *)
Qed.

(* The two key components of logic programming are 

    _backtracking_ and _unification_
 
 * To see these techniques in action, consider this further
 * silly example.  Here our candidate proof steps will be reflexivity and
 * quantifier instantiation. *)

Check ex_intro.

Example seven_minus_three : exists x, x + 3 = 7.
Proof.
  (* For explanatory purposes, let us simulate a user with minimal understanding
   * of arithmetic.  We start by choosing an instantiation for the quantifier.
   * It is relevant that [ex_intro] is the proof rule for existential-quantifier
   * instantiation. *)

  apply ex_intro with 0.
  Fail reflexivity.

  (* This seems to be a dead end.  Let us _backtrack_ to the point where we ran
   * [apply] and make a better alternative choice. *)

Restart.
  apply ex_intro with 4.
  reflexivity.
Qed.

(* The above was a fairly tame example of backtracking. In general, any node in
 * an under-construction proof tree may be the destination of backtracking an
 * arbitrarily large number of times, as different candidate proof steps are
 * found not to lead to full proof trees, within the depth bound passed to [auto].
 *
 * Next we demonstrate unification, which will be easier when we switch to the
 * relational formulation of addition. *)

Example seven_minus_three' : exists x, plusR x 3 7.
Proof.
  (* We could attempt to guess the quantifier instantiation manually as before,
   * but here there is no need.  Instead of [apply], we use [eapply], which
   * proceeds with placeholder _unification variables_ standing in for those
   * parameters we wish to postpone guessing. *)

  eapply ex_intro.
  (* [eapply H]: like [apply], but works when it is not obvious how to
   * instantiate the quantifiers of theorem/hypothesis [H].  Instead,
   * placeholders are inserted for those quantifiers, to be determined
   * later. *)

  (* Now we can finish the proof with the right applications of [plusR]'s
   * constructors.  Note that new unification variables are being generated to
   * stand for new unknowns. *)

  apply PlusS.
  apply PlusS. apply PlusS. apply PlusS.
  apply PlusO.

  (* The [auto] tactic will not perform these sorts of steps that introduce
   * unification variables, but the [eauto] tactic will.  It is helpful to work
   * with two separate tactics, because proof search in the [eauto] style can
   * uncover many more potential proof trees and hence take much longer to
   * run. *)

Restart.
  auto 6.
  info_eauto 6.
Qed.

Print seven_minus_three'.

(* This proof gives us our first example where logic programming simplifies
 * proof search compared to functional programming.  
 
 * In general, functional programs are only meant to be run in a single
 * direction; a function has disjoint sets of inputs and outputs.
 * In the last example, we effectively ran a logic program backwards, 
 * deducing an input that gives rise to a certain output.  
 
 * The same works for deducing an unknown value of the other input. *)

Example seven_minus_four' : exists x y, plusR x y 7 /\ x <> 0 /\ y <> 6.
Proof.
  eauto 8.
Qed.

Print seven_minus_four'.

(* _Connecting Functional Programs and Logical Proofs_

 * By proving the right auxiliary facts, we can reason about specific functional
 * programs in the same way as we did above for a logic program. 
 
 * Recall the relational definition of [plusR] *)
 
Print plusR.

(* Let us prove that the constructors of [plusR] have natural interpretations 
 * as lemmas about [plus]. *)

SearchRewrite (O + _).

(* The command [Hint Immediate] asks [auto] and [eauto] to consider this lemma
 * as a candidate step for any leaf of a proof tree, meaning that all premises
 * of the rule need to match hypotheses. *)

Hint Immediate plus_O_n.

(* Proof search will try [simple apply plus_O_n; trivial] whenever it is
 * applicable. *)

(* The counterpart to [PlusS] we will prove ourselves. *)

Print PlusS.

Lemma plusS : forall n m r,
  n + m = r
  -> S n + m = S r.
Proof.
  linear_arithmetic.
Qed.

(* The command [Hint Resolve] adds a new candidate proof step, to be attempted
 * at any level of a proof tree, not just at leaves. *)

Hint Resolve plusS.

(* Proof search will try [simple apply plusS] whenever it is applicable. *)

(* Now that we have registered the proper hints, we can replicate our previous
 * examples with the normal, functional addition [plus]. *)

Example seven_minus_three'' : exists x, x + 3 = 7.
Proof.
  debug eauto 6.
Qed.

Example seven_minus_four : exists x, 4 + x = 7.
Proof.
  info_eauto 6.
Qed.

(* This new _hint database_ is far from a complete decision procedure, 
 * as we see in a further example that [eauto] does not finish. *)

Example seven_minus_four_zero : exists x, 4 + x + 0 = 7.
Proof.
  debug eauto 6.
Abort.

(* A further lemma will be helpful. *)

Lemma plusO : forall n m,
  n = m
  -> n + 0 = m.
Proof.
  linear_arithmetic.
Qed.

Hint Resolve plusO.

(* Note that, if we consider the inputs to [plus] as the inputs of a
 * corresponding logic program, the new rule [plusO] introduces an ambiguity. *)

Check plus_O_n.
Check plusO.

(* For instance, a sum [0 + 0] would match both of [plus_O_n] and [plusO],
 * depending on which operand we focus on.  This ambiguity may increase the
 * number of potential search trees, slowing proof search, but semantically it
 * presents no problems, and in fact it leads to an automated proof of the
 * present example. *)

Example seven_minus_four_zero : exists x, 4 + x + 0 = 7.
Proof.
  info_eauto 7.
Qed.

(* Just how much damage can be done by adding hints that grow the space of
 * possible proof trees?  A classic gotcha comes from unrestricted use of
 * transitivity, as embodied in this library theorem about equality: *)

Check eq_trans.

(* Hints are scoped over sections, so let us enter a section to contain the
 * effects of an unfortunate hint choice. *)

Section slow.
  Hint Resolve eq_trans.

  (* The following fact is false, but that does not stop [eauto] from taking a
   * very long time to search for proofs of it.  We use the handy [Time] command
   * to measure how long a proof step takes to run.  None of the following steps
   * make any progress. *)

  Example zero_minus_one : exists x, 1 + x = 0.
    Time eauto 1.
    Time eauto 2.
    Time eauto 3.
    Time eauto 4.
    Time eauto. (* 5 *)

    (* We see worrying exponential growth in running time, and the [debug]
     * tactical helps us see where [eauto] is wasting its time, outputting a
     * trace of every proof step that is attempted.  The rule [eq_trans] applies
     * at every node of a proof tree, and [eauto] tries all such positions. *)

    debug eauto 4.
  Abort.
End slow.

(* Sometimes, though, transitivity is just what is needed to get a proof to go
 * through automatically with [eauto].  For those cases, we can use named
 * _hint databases_ to segregate hints into different groups that may be called
 * on as needed.  Here we put [eq_trans] into the database [slow]. *)

Hint Resolve eq_trans : slow.

Example from_one_to_zero : exists x, 1 + x = 0.
Proof.
  Time eauto.
  (* This [eauto] fails to prove the goal, but at least it takes substantially
   * less than the ~1.2 seconds required above! *)
Abort.

(* When we _do_ need transitivity, we ask for it explicitly. *)

Example needs_trans : forall x y, 1 + x = y
  -> y = 2
  -> exists z, z + x = 3.
Proof.
  info_eauto with slow.
Restart.
  intro.
intro.
intro.
intro.
simple eapply ex_intro.
 simple apply plusS.
  simple eapply eq_trans.
   exact H.
   exact H0.
Qed.

(** * Searching for Underconstrained Values *)

(* Recall the definition of the list length function. *)

Print Datatypes.length.

(* This function is easy to reason about in the forward direction, computing
 * output from input. *)

Example length_1_2 : length (1 :: 2 :: nil) = 2.
Proof.
  info_auto.
Qed.

Print length_1_2.

(* As in the last section, we will prove some lemmas to recast [length] in
 * logic-programming style, to help us compute inputs from outputs. *)
 
(* Here is the relational definition of length *)
Inductive lengthR {A : Type} : list A -> nat -> Prop :=
| lengthO : lengthR nil 0
| lengthS : forall h t n, lengthR t n -> lengthR (h::t) (S n).

(* As before, connect the logical version to the similar 
 * functional version *)
Theorem length_O : forall A, length (@nil A) = O.
Proof.
  simplify; equality.
Qed.

Theorem length_S : forall A (h : A) t n,
  length t = n
  -> length (h :: t) = S n.
Proof.
  simplify; equality.
Qed.

Hint Resolve length_O length_S.

(* Let us apply these hints to prove that a [list nat] of length 2 exists.
 * (Here we register [length_O] with [Hint Resolve] instead of [Hint Immediate]
 * merely as a convenience to use the same command as for [length_S]; [Resolve]
 * and [Immediate] have the same meaning for a premise-free hint.) *)

Example length_is_2 : exists ls : list nat, length ls = 2.
Proof.
  eauto.

  (* Coq leaves for us two subgoals to prove... [nat]?!  We are being asked to
   * show that natural numbers exists.  Why?  Some unification variables of that
   * type were left undetermined, by the end of the proof.  Specifically, these
   * variables stand for the 2 elements of the list we find.  Of course it makes
   * sense that the list length follows without knowing the data values.  In Coq
   * 8.6, the [Unshelve] command brings these goals to the forefront, where we
   * can solve each one with [exact O], but usually it is better to avoid
   * getting to such a point.
   *
   * To debug such situations, it can be helpful to print the current internal
   * representation of the proof, so we can see where the unification variables
   * show up. *)

  Show Proof.
Abort.

(* Paradoxically, we can make the proof-search process easier by constraining
 * the list further, so that proof search naturally locates appropriate data
 * elements by unification.  The library predicate [Forall] will be helpful. *)

Check Forall.

Example length_is_2 : exists ls : list nat, length ls = 2
  /\ Forall (fun n => n >= 0) ls.
Proof.
  eauto 9.
Qed.

(* We can see which list [eauto] found by printing the proof term. *)

Print length_is_2.

(* The elements chosen for the list is [0] *)

(* Let us try one more, fancier example.  First, we use a standard higher-order
 * function to define a function for summing all data elements of a list. *)

Definition sum := fold_right plus O.

(* Another basic lemma will be helpful to guide proof search. *)

Check plusO.

Lemma plusO' : forall n m,
  n = m
  -> 0 + n = m.
Proof.
  linear_arithmetic.
Qed.

Hint Resolve plusO'.

(* Finally, we meet [Hint Extern], the command to register a custom hint.  That
 * is, we provide a pattern to match against goals during proof search.
 * Whenever the pattern matches, a tactic (given to the right of an arrow [=>])
 * is attempted.  Below, the number [1] gives a priority for this step.  Lower
 * priorities are tried before higher priorities, which can have a significant
 * effect on proof search time, i.e. when we manage to give lower priorities to
 * the cheaper rules. *)

Hint Extern 1 (sum _ = _) => simplify.

(* Now we can find a length-2 list whose sum is 0. *)

Example length_and_sum : exists ls : list nat, length ls = 2
  /\ sum ls = O.
Proof.
  info_eauto 7.
Restart.
simple eapply ex_intro.
 simple apply conj.
  simple apply length_S.
   simple apply length_S.
    simple apply length_O.
    (*external*) simplify.
     simple apply plusO'.
      simple apply plus_O_n ; trivial.
Qed.

Print length_and_sum.

(* Printing the proof term shows the unsurprising list that is found.  Here is
 * an example where it is less obvious which list will be used.  Can you guess
 * which list [eauto] will choose? *)

Example length_and_sum' : exists ls : list nat, length ls = 5
  /\ sum ls = 42.
Proof.
  eauto 15.
Qed.

Print length_and_sum'.

(* We will give away part of the answer and say that the above list is less
 * interesting than we would like, because it contains too many zeroes.  A
 * further constraint forces a different solution for a smaller instance of the
 * problem. *)

Example length_and_sum'' : exists ls : list nat, length ls = 2
  /\ sum ls = 3
  /\ Forall (fun n => n <> 0) ls.
Proof.
  eauto 11.
Qed.

Print length_and_sum''.

(* We could continue through exercises of this kind, but even more interesting
 * than finding lists automatically is finding _programs_ automatically. *)


(** * Synthesizing Programs *)

(* Here is a simple syntax type for arithmetic expressions, similar to those we
 * have used several times before.  In this case, we allow expressions to
 * mention exactly one distinguished variable. *)

Inductive exp : Set :=
| Const (n : nat)
| Var
| Plus (e1 e2 : exp).

(* An inductive relation specifies the semantics of an expression, relating a
 * variable value and an expression to the expression value. *)

Inductive eval (var : nat) : exp -> nat -> Prop :=
| EvalConst : forall n, eval var (Const n) n
| EvalVar : eval var Var var
| EvalPlus : forall e1 e2 n1 n2, 
       eval var e1 n1
    -> eval var e2 n2
    -> eval var (Plus e1 e2) (n1 + n2).

Hint Constructors eval.

(* We can use [auto] to execute the semantics for specific expressions. *)

Example eval1 : forall var, 
  eval var (Plus Var (Plus (Const 8) Var)) 
           (var + (8 + var)).
Proof.
  info_eauto.
Restart.
intro.
simple apply EvalPlus.
 simple apply EvalVar.
 simple apply EvalPlus.
  simple apply EvalConst.
  simple apply EvalVar.
Qed.

(* Unfortunately, just the constructors of [eval] are not enough to prove
 * theorems like the following, which depends on an arithmetic identity. *)

Example eval1' : forall var, 
  eval var (Plus Var (Plus (Const 8) Var)) 
           (2 * var + 8).
Proof.
  eauto.
Restart.
  intros.
  apply EvalPlus.
   (* cannot proceed further *)
Abort.

(* To help prove [eval1'], we prove an alternative version of [EvalPlus] that
 * inserts an extra equality premise.  This sort of staging is helpful to get
 * around limitations of [eauto]'s unification. 
 
 * With the alternative version below, to prove the first
 * two premises, [eauto] is given free reign in deciding the values of [n1] and
 * [n2], while the third premise can then be proved by [reflexivity], no matter
 * how each of its sides is decomposed as a tree of additions. *)

Check EvalPlus.

Theorem EvalPlus' : forall var e1 e2 n1 n2 n, 
     eval var e1 n1
  -> eval var e2 n2
  -> n1 + n2 = n
  -> eval var (Plus e1 e2) n.
  (* One way to think about this is that we're extending the
     evaluator with more rules. *)
Proof.
  simplify.
  subst.
  auto.
Qed.

Hint Resolve EvalPlus'.

(* Further, we instruct [eauto] to apply [ring], via [Hint Extern].  We should
 * try this step for any equality goal. *)

Section use_ring.
  Hint Extern 1 (_ = _) => ring.

  (* Now we can return to [eval1'] and prove it automatically. *)

  Example eval1' : forall var, 
    eval var (Plus Var (Plus (Const 8) Var)) 
             (2 * var + 8).
  Proof.
    info_eauto.
  Restart.
  intro.
  simple eapply EvalPlus'.
   simple apply EvalVar.
   simple apply EvalPlus.
    simple apply EvalConst.
    simple apply EvalVar.
    (*external*) ring.
  Qed.

  (* Now we are ready to take advantage of logic programming's flexibility by
   * searching for a program (arithmetic expression) that always evaluates to a
   * particular symbolic value. *)

  Example synthesize1 : exists e, forall var, eval var e (var + 7).
  Proof.
    eauto.
  Qed.

  Print synthesize1.

  (* Here are two more examples showing off our program-synthesis abilities. *)

  Example synthesize2 : exists e, forall var, 
    eval var e (2 * var + 8).
  Proof.
    eauto.
  Qed.

  Print synthesize2.

  Example synthesize3 : exists e, forall var, 
    eval var e (3 * var + 42).
  Proof.
    eauto.
  Qed.

  Print synthesize3.
End use_ring.