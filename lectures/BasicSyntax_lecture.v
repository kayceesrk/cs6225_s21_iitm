(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 2: Basic Program Syntax
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

Module ArithWithConstants.

  Inductive arith : Set :=
  | Const (n : nat)
  | Plus (e1 e2 : arith)
  | Times (e1 e2 : arith).

  (* Here are a few examples of specific expressions. *)
  Example ex1 := Const 42.
  Example ex2 := Plus (Const 1) (Times (Const 2) (Const 3)).

  Fixpoint size (e : arith) : nat :=
    match e with
    | Const _ => 1
    | Plus e1 e2 => 1 + size e1 + size e2
    | Times e1 e2 => 1 + size e1 + size e2
    end.

  (* Here's how to run a program (evaluate a term) in Coq. *)
  Compute size ex1.
  Compute size ex2.

  (* What's the longest path from the root of a syntax tree to a leaf? *)
  Fixpoint depth (e : arith) : nat :=
    match e with
    | Const _ => 1
    | Plus e1 e2 => 1 + max (depth e1) (depth e2)
    | Times e1 e2 => 1 + max (depth e1) (depth e2)
    end.

  Compute depth ex1.
  Compute depth ex2.

  (* Size is an upper bound on depth. *)
  Theorem depth_le_size : forall e, depth e <= size e.
  Proof.
    induct e.
    (* [induct x]: where [x] is a variable in the theorem statement,
     *   structure the proof by induction on the structure of [x].
     *   You will get one generated subgoal per constructor in the
     *   inductive definition of [x].  (Indeed, it is required that 
     *   [x]'s type was introduced with [Inductive].) 
     *
     * c.f [induct] tactic. *)
     

    simplify.
    (* [simplify]: simplify throughout the goal, applying the definitions of
     *   recursive functions directly.  That is, when a subterm
     *   matches one of the [match] cases in a defining [Fixpoint],
     *   replace with the body of that case, then repeat. 
     *
     * c.f [simpl] tactic. *)
     
     
    linear_arithmetic.
    (* [linear_arithmetic]: a complete decision procedure for linear arithmetic.
     *   Relevant formulas are essentially those built up from
     *   variables and constant natural numbers and integers
     *   using only addition, with equality and inequality
     *   comparisons on top.  (Multiplication by constants
     *   is supported, as a shorthand for repeated addition.) *)

    simplify.
    linear_arithmetic.
    (* [linear_arithmetic] is quite clever in how it rewrites induction hypotheses.
       Try using [rewrite] tactic here. *)

    simplify.
    linear_arithmetic.
  Qed.

  Theorem depth_le_size_snazzy : forall e, depth e <= size e.
  Proof.
    induct e; simplify; linear_arithmetic.
  Qed.

  (* A silly recursive function: swap the operand orders of all binary operators. *)
  Fixpoint commuter (e : arith) : arith :=
    match e with
    | Const _ => e
    | Plus e1 e2 => Plus (commuter e2) (commuter e1)
    | Times e1 e2 => Times (commuter e2) (commuter e1)
    end.

  Compute commuter ex1.
  Print ex2.
  Compute commuter ex2.

  (* [commuter] has all the appropriate interactions with other functions (and itself). *)

  Theorem size_commuter : forall e, size (commuter e) = size e.
  Proof.
    induct e; simplify; linear_arithmetic.
  Qed.

  Theorem depth_commuter : forall e, depth (commuter e) = depth e.
  Proof.
    induct e; simplify; linear_arithmetic.
  Qed.

  Theorem commuter_inverse : forall e, commuter (commuter e) = e.
  Proof.
    induct e; simplify; equality.
    (* [equality]: a complete decision procedure for the theory of equality
     *   and uninterpreted functions.  That is, the goal must follow
     *   from only reflexivity, symmetry, transitivity, and congruence
     *   of equality, including that functions really do behave as functions. *)
  Qed.

End ArithWithConstants.








































(* Let's shake things up a bit by adding variables to expressions.
 * Note that all of the automated proof scripts from before will keep working
 * with no changes!  That sort of "free" proof evolution is invaluable for
 * theorems about real-world compilers, say. *)
Module ArithWithVariables.

  Inductive arith : Set :=
  | Const (n : nat)
  | Var (x : var) (* <-- this is the new constructor! *)
  | Plus (e1 e2 : arith)
  | Times (e1 e2 : arith).


  Example ex1 := Const 42.
  Example ex2 := Plus (Const 1) (Times (Var "x") (Const 3)).

  Fixpoint size (e : arith) : nat :=
    match e with
    | Const _ => 1
    | Var _ => 1
    | Plus e1 e2 => 1 + size e1 + size e2
    | Times e1 e2 => 1 + size e1 + size e2
    end.

  Compute size ex1.
  Compute size ex2.

  Fixpoint depth (e : arith) : nat :=
    match e with
    | Const _ => 1
    | Var _ => 1
    | Plus e1 e2 => 1 + max (depth e1) (depth e2)
    | Times e1 e2 => 1 + max (depth e1) (depth e2)
    end.

  Compute depth ex1.
  Compute depth ex2.

  Theorem depth_le_size : forall e, depth e <= size e.
  Proof.
    induct e; simplify; linear_arithmetic.
  Qed.

  Fixpoint commuter (e : arith) : arith :=
    match e with
    | Const _ => e
    | Var _ => e
    | Plus e1 e2 => Plus (commuter e2) (commuter e1)
    | Times e1 e2 => Times (commuter e2) (commuter e1)
    end.

  Compute commuter ex1.
  Compute commuter ex2.

  Theorem size_commuter : forall e, size (commuter e) = size e.
  Proof.
    induct e; simplify; linear_arithmetic.
  Qed.

  Theorem depth_commuter : forall e, depth (commuter e) = depth e.
  Proof.
    induct e; simplify; linear_arithmetic.
  Qed.

  Theorem commuter_inverse : forall e, commuter (commuter e) = e.
  Proof.
    induct e; simplify; equality.
  Qed.



































Check arith.
Check Set.
Check Prop.
Check Type. 



  (* We use an infix operator [==v] for equality tests on strings.*)
  Fixpoint substitute (inThis : arith) (replaceThis : var) (withThis : arith) : arith :=
    match inThis with
    | Const _ => inThis
    | Var x => if x ==v replaceThis then withThis else inThis
    | Plus e1 e2 => 
        Plus (substitute e1 replaceThis withThis) 
             (substitute e2 replaceThis withThis)
    | Times e1 e2 => 
        Times (substitute e1 replaceThis withThis) 
              (substitute e2 replaceThis withThis)
    end.

  (* An intuitive property about how much [substitute] might increase depth. *)
  Theorem substitute_depth : forall replaceThis withThis inThis,
    depth (substitute inThis replaceThis withThis) <= 
    depth inThis + depth withThis.
  Proof.
    induct inThis.

    simplify.
    linear_arithmetic.

    simplify.
    cases (x ==v replaceThis).
    (* [cases e]: break the proof into one case for each 
     * constructor that might have been used to build the 
     * value of expression [e].  In the special case where
     * [e] essentially has a Boolean type, we consider 
     * whether [e] is true or false. 
     *
     * [cases] is like [destruct] but more powerful
     *)
    linear_arithmetic.
    
    simplify.
    linear_arithmetic.

    simplify.
    linear_arithmetic.

    simplify.
    linear_arithmetic.
  Qed.
  
  (* A stronger property about substitution. [<=] replaced by [<] *)
  Theorem substitute_depth' : forall replaceThis withThis inThis,
    depth (substitute inThis replaceThis withThis) < depth inThis + depth withThis.
  Proof.
    induct inThis.

    simplify.
    cases withThis; simplify; linear_arithmetic.

    simplify.
    cases (x ==v replaceThis).
    (* [cases e]: break the proof into one case for each constructor that might have
     *   been used to build the value of expression [e].  In the special case where
     *   [e] essentially has a Boolean type, we consider whether [e] is true or false. *)
    linear_arithmetic.
    simplify.
    cases withThis; simplify; linear_arithmetic.

    simplify.
    linear_arithmetic.

    simplify.
    linear_arithmetic.
  Qed.







































  (* Let's get fancier about automation, using [match goal] to pattern-match the goal
   * and decide what to do next!
   * The [|-] syntax separates hypotheses and conclusion in a goal.
   * The [context] syntax is for matching against *any subterm* of a term.*)
  Theorem substitute_depth_snazzy : forall replaceThis withThis inThis,
    depth (substitute inThis replaceThis withThis) <= depth inThis + depth withThis.
  Proof.
    induct inThis; simplify;
    (* [try] tactical attempts to apply a tactic, and ignores failures *)
    try match goal with
        | [ |- context[if ?a ==v ?b then _ else _] ] => cases (a ==v b); simplify
        end;
    linear_arithmetic.
  Qed.

  (* A silly self-substitution has no effect. *)
  Theorem substitute_self : forall replaceThis inThis,
    substitute inThis replaceThis (Var replaceThis) = inThis.
  Proof.
    induct inThis; simplify;
    try match goal with
        | [ |- context[if ?a ==v ?b then _ else _] ] => cases (a ==v b); simplify
        end; equality.
  Qed.

  (* We can do substitution and commuting in either order. *)
  Theorem substitute_commuter : forall replaceThis withThis inThis,
    commuter (substitute inThis replaceThis withThis)
    = substitute (commuter inThis) replaceThis (commuter withThis).
  Proof.
    induct inThis; simplify;
    try match goal with
        | [ |- context[if ?a ==v ?b then _ else _] ] => cases (a ==v b); simplify
        end; equality.
  Qed.




































  (* *Constant folding* is one of the classic compiler optimizations.
   * We repeatedly find opportunities to replace fancier expressions
   * with known constant values. *)
  Fixpoint constantFold (e : arith) : arith :=
    match e with
    | Const _ => e
    | Var _ => e
    | Plus e1 e2 =>
      let e1' := constantFold e1 in
      let e2' := constantFold e2 in
      match e1', e2' with
      | Const n1, Const n2 => Const (n1 + n2)
      | Const 0, _ => e2'
      | _, Const 0 => e1'
      | _, _ => Plus e1' e2'
      end
    | Times e1 e2 =>
      let e1' := constantFold e1 in
      let e2' := constantFold e2 in
      match e1', e2' with
      | Const n1, Const n2 => Const (n1 * n2)
      | Const 1, _ => e2'
      | _, Const 1 => e1'
      | Const 0, _ => Const 0
      | _, Const 0 => Const 0
      | _, _ => Times e1' e2'
      end
    end.
    
  Example ex3 := Times (Plus (Const 0) (Var "x")) (Const 1).
  Compute constantFold ex3.

  (* This is supposed to be an *optimization*, so it had better not *increase*
   * the size of an expression!
   * There are enough cases to consider here that we skip straight to
   * the automation.
   * A new scripting construct is [match] patterns with dummy bodies.
   * Such a pattern matches *any* [match] in a goal, over any type! *)
  Theorem size_constantFold : forall e, size (constantFold e) <= size e.
  Proof.
    (*
    induct e.
    - simplify. linear_arithmetic.
    - simplify. linear_arithmetic.
    - simplify. cases (constantFold e1). cases n. cases (constantFold e2). 
      + simplify. linear_arithmetic. 
      + simplify. linear_arithmetic. 
      + simplify. linear_arithmetic. 
      + simplify. linear_arithmetic.
      + simplify. cases (constantFold e2).
        * simplify. linear_arithmetic.
        * simplify. linear_arithmetic. 
    *)
    induct e; simplify;
    (* [repeat] tactical loop repeats a tactic until it fails. *)
    repeat match goal with
           | [ |- context[match ?E with _ => _ end] ] => cases E; simplify
           end; linear_arithmetic.
  Qed.

  (* Business as usual, with another commuting law *)
  Theorem commuter_constantFold : forall e, commuter (constantFold e) = constantFold (commuter e).
  Proof.
    induct e; simplify;
    repeat match goal with
           | [ |- context[match ?E with _ => _ end] ] => cases E; simplify
           | [ H : ?f _ = ?f _ |- _ ] => invert H
           | [ |- ?f _ = ?f _ ] => f_equal
           end; equality || linear_arithmetic.
    (* [f_equal]: when the goal is an equality between two applications of
     *   the same function, switch to proving that the function arguments are
     *   pairwise equal.
     * [invert H]: replace hypothesis [H] with other facts that can be deduced
     *   from the structure of [H]'s statement.  This is admittedly a fuzzy
     *   description for now; we'll learn much more about the logic shortly!
     *   Here, what matters is that, when the hypothesis is an equality between
     *   two applications of a constructor of an inductive type, we learn that
     *   the arguments to the constructor must be pairwise equal. *)
  Qed.

(* More stuff in BasicSyntax.v. Do read the rest of the lecture. *)

End ArithWithVariables.
