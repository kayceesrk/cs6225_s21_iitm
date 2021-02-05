(** 
 * Logic in Coq
 **)

(**********************************************************************)

(* Propositions and proofs *)

Check list.
(* [list] is a type-level function *)

Definition natlist : Type := list nat.
(* explicit application of type-level functions *)
Check natlist.

(* What, then, is the type of a theorem? *)

Theorem obvious_fact : 1 + 1 = 2.
Proof. trivial. Qed.
Check obvious_fact.

(**
Coq responds:
<<
obvious_fact : 1 + 1 = 2
>>

If [1+1 = 2] is a type, what are its values? 

    Proofs of [1 + 1 = 2]!

There might be many such proofs; here are two: 

- reduce [1+1] to [2], then note that [x=x]. 

- subtract [1] from both sides 
    resulting in [1 + 1 - 1 = 2 - 1]
  reduce both sides to [1], 
  then note that [x = x]. 

What proof does Coq have for [1 + 1 = 2]? *)

Print obvious_fact.

(**
Coq responds:
<<
obvious_fact = eq_refl : 1 + 1 = 2
>>
So what is [eq_refl]?
*)

Print eq_refl.

(** Amidst all the output that produces, you will spy 
<< 
eq_refl : x = x 
>> 
That is, [eq_refl] has type [x = x]. 
*)

(**********************************************************************)

(**
** [Prop] and [Set]
*)

Check 42.

Check nat.

(**
The Coq documentation describes [Set] as being the type of _program specifications_, which describe
computations.
*)

Check Set.

(* What is the type of [1 + 1 = 2]? *)

Check 1 + 1 = 2.

(**
[Prop] is the type of all the things that can be proved (not necessarily hold).
*)

Check 1 + 1 = 3.

Check Prop.

Check true.

Check True.

(**
The type of [Prop] is also [Type].
*)

(* Consider *)

Check 1 + 1.
Check 3.
Check 1 + 1 = 3.

(* [=] takes two [nat]s and returns a [Prop]. 

   What can we learn about it? *)

Locate "=".

(**
Coq tells us two possible meanings for [=], and the second is what we want: 
<<
"x = y" := eq x y
>>
*)

Check @eq.

(* [eq] builds a proposition that can be proved using two values of the same type *)

Check eq (fun x => x + 1) (fun n => n + 2 - 1).

Theorem t1 : eq (fun x => x + 1) (fun n => n + 2 - 1).
Proof.
Admitted.

(**********************************************************************)

(**
** Propositional logic

Here are the _connectives_ in Coq:

- Implication: [P -> Q].
- Conjunction: [P /\ Q].
- Disjunction: [P \/ Q].
- Negation: [~P].

* None of these connectives are baked in, but encoded.
*)

Check and.
Check or.
Check not.

(**
<<
and : Prop -> Prop -> Prop
or  : Prop -> Prop -> Prop
not : Prop -> Prop
>>

Observe that we use [->] as implication but also as the type of functions.

This is not an accident!

[P -> Q] can be thought of as:

  - The type of functions that take a [P] and return [Q]
  - A proposition that asserts [P] implies [Q]
  
They are the same in Coq! Let's see this in action.

*)

(**********************************************************************)

(** Implication *)

Theorem p_implies_p : forall P: Prop, P -> P.

(** 
So why does this proposition hold? If you've already assumed [P], then
necessarily [P] follows from your assumptions:  that's what it means to be an
assumption.  

The Coq proof below uses that reasoning. 
*)

Proof.
    intros P P_assumed. 
    assumption. (* new tactic *)
Qed.

(* Let's look at the type of [p_implies_p]. *)

Check p_implies_p.

(** What is that evidence?  We can use [Print] to find out: *)

Print p_implies_p.

(** 
Coq responds
<<
p_implies_p = 
fun (P : Prop) (P_assumed : P) => P_assumed
     : forall P : Prop, P -> P
>>

The proof is essentially the identity function for a given [P] that we want to prove. 

Can also be done directly as a [Definition]:
*)

Definition p_implies_p_direct : forall P:Prop, P -> P := 
  fun p ev_p => ev_p.

(**
  + Rarely do we construct such direct proofs
  + Tactics help us construct complicated proofs.
*)

Theorem syllogism : forall P Q : Prop, 
  (P -> Q) -> P -> Q.

(**
How would you convince a human that this theorem holds?  
  + Assume that [P -> Q].  
  + Also assume [P].  Since
  + [P] holds, and since [P] implies [Q], we know that [Q] must also hold.

The Coq proof below uses that style of argument.
*)

Proof.
  intros P Q evPimpQ evP.
  apply evPimpQ. (* new tactic *)
  assumption.
Qed.

(** 
  + [apply] applies given evidence to goal. 
  + Does _backward reasoning_

Let's look at the proof that these tactics cause Coq to create:
*)

Print syllogism.

(**
We see that
<<
syllogism = 
fun (P Q : Prop) (evPimpQ : P -> Q) (evP : P) => evPimpQ evP
     : forall P Q : Prop, (P -> Q) -> P -> Q
>>

Equivalent to the OCaml function

let apply f v = f v
*)

Theorem syllogism' : forall P Q : Prop, 
  (P -> Q) -> P -> Q.
Proof.
  intros.
  apply H in H0. 
  (* Can also [apply] to assumptions to do _forwards reasoning *)
  assumption.
Qed.


Theorem imp_trans : forall P Q R : Prop,
  (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R evPimpQ evQimpR.
  intros evP.
  apply evQimpR.
  apply evPimpQ.
  assumption.
Qed.

(** Let's look at the resulting proof: *)

Print imp_trans.

(**
Coq says
<<
imp_trans = 
fun (P Q R : Prop) (evPimpQ : P -> Q) (evQimpR : Q -> R) (evP : P) =>
evQimpR (evPimpQ evP)
     : forall P Q R : Prop, (P -> Q) -> (Q -> R) -> P -> R
>>

Equivalent to the OCaml function

let composition f g v = g (f v)

(**********************************************************************)

** Conjunction

Now we turn our attention to the conjunction connective.  Here's
a first theorem to prove.
*)

Theorem and_fst : forall P Q, P /\ Q -> P.

(** Why does that hold, intuitively?
     + Suppose we have evidence of [P /\ Q], we have evidence of [P].
     + Use that evidence of [P] to show [P] holds.
*)

Proof.
    intros P Q PandQ.
    destruct PandQ as [P_holds Q_holds]. 
    assumption.
Qed.

(** Let's look at the proof of [and_fst]. *)

Print and_fst.

(**
Coq says that 
<<
and_fst = 
fun (P Q : Prop) (PandQ : P /\ Q) =>
match PandQ with
| conj P_holds _ => P_holds
end
     : forall P Q : Prop, P /\ Q -> P
>>

What is [conj]?
*)

Check conj.

Locate "/\".

Print and.

(* Takeaway: In order to construct a proof for [P /\ Q], you need [P] and [Q] and use the [conj] constructor to put them together *)

Theorem and_snd : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q PandQ.
  destruct PandQ.
  assumption.
Qed.

Print and_snd.

(** Here is another proof involving [and]. *)

Theorem and_ex : 42=42 /\ 43=43.

(** Why does that hold, intuitively?  Because equality is reflexive, regardless
of how many times we connect that fact with [/\]. *)

Proof. 
  split. (* new tactic *)
  trivial. trivial.
Qed.

(* What is [and_ex]? *)

Print and_ex.

(**
Coq responds:
<<
and_ex = conj eq_refl eq_refl
     : 42 = 42 /\ 43 = 43
>>

So [and_ex] is [conj] applied to [eq_refl] as its first argument and [eq_refl] as its second argument.
*)


(* As another example of conjunction, let's prove that it is commutative. *)

Theorem and_comm: forall P Q, P /\ Q -> Q /\ P.
Proof.
    intros P Q PandQ. 
    destruct PandQ.
    split. 
    all: assumption.
Qed.

Print and_comm.

(**********************************************************************)

(** Disjunction

Let's start with disjunction by proving a theorem very similar to the first
theorem we proved for conjunction: *)

Theorem or_left : forall (P Q : Prop), P -> P \/ Q.

(** As always, what's the intuition? 

Let's formalize that argument in Coq. *)

Proof.
    intros P Q P_holds. 
    left. (* new tactic *) 
    assumption.
Qed.

Print or_left.

(**
Coq responds
<<
or_left = 
fun (P Q : Prop) (P_holds : P) => or_introl P_holds
     : forall P Q : Prop, P -> P \/ Q
>>

That function's arguments are no mystery by now, but what is its body?
We need to find out more about [or_introl].
*)

Locate "\/".
(** "\/" is infix notation for [or A B] *)

Print or_introl.
(* [or_introl] is one of two constructors of the type [or]:
<<
Inductive or (A B : Prop) : Prop :=
    or_introl : A -> A \/ B 
  | or_intror : B -> A \/ B
>>
*)


Theorem or_comm : forall P Q, P \/ Q -> Q \/ P.

(** Why does this hold?

That's what the Coq proof below does. *)

Proof.
    intros P Q PorQ.
    destruct PorQ.
    - right. assumption.
    - left. assumption.
Qed. 

Print or_comm.

(**
Coq responds
<<
or_comm = 
fun (P Q : Prop) (PorQ : P \/ Q) =>
match PorQ with
| or_introl H => or_intror H
| or_intror H => or_introl H
end
     : forall P Q : Prop, P \/ Q -> Q \/ P)
>>

Next, let's prove a theorem involving both conjunction and disjunction. *)


Theorem or_distr_and : forall P Q R, 
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).

Proof.
  intros P Q R PorQR.
  destruct PorQR.
  
  - split.
    + left. assumption.
    + left. assumption.
  - destruct H.
    split.
    + right. assumption.
    + right. assumption.
Qed.

(** We can make the proof shorter with [;] *)

Theorem or_distr_and_shorter : forall P Q R, 
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R PorQR.
  destruct PorQR.
  - split; left; assumption.
  - destruct H.
    split; right; assumption.
Qed.


(**********************************************************************)

(** [False] and [True]

[False] is the proposition that can never hold

Here's the definition of [False]: *)

Print False.

(**
Coq responds
<<
Inductive False : Prop :=  
>>

Has no constructors. And hence, we cannot provide evidence that [False] holds.

Let's prove the Principle of Explosion. *)

Theorem explosion : forall P:Prop, False -> P.
Proof.
    intros P false_holds. 
    contradiction. (* new tactic *)
Qed.

(** The second line of the proof uses a new tactic, [contradiction].  This
tactic looks for any contradictions or assumptions of [False], and uses those to
conclude the proof.  In this case, it immediately finds [False] as an assumption
named [false_holds].*)

Print explosion.
Print False_ind.

(**
  + The [return P] in the pattern match above is a type annotation 
  + [False_ind] uses the evidence of [False] to return the evidence for any [P].
*)

(* We can directly define this function *)

Definition explosion' : forall (P:Prop), False -> P := 
  fun (P : Prop) (f (* no valid values for [f] *) : False) => 
    match f with
    end.

(** We can never prove [P -> P /\ False], because there is no way to construct the evidence for the right side. *)

Theorem p_imp_p_and_false : forall P:Prop, P -> P /\ False.
Proof.
  intros P P_holds. split. assumption.  (* now we're stuck *)
Abort.

(** But we can always prove [P -> P \/ False] by just focusing on the non-false
part of the disjunction. *)

Theorem p_imp_p_or_false : forall P:Prop, P -> P \/ False.
Proof.
  intros P P_holds. left. assumption.
Qed.

(** [True] is the proposition that is always true *)

Print True.

Theorem p_imp_p_and_true : forall P:Prop, P -> P /\ True.
Proof.
  intros P P_holds. split. assumption. 
  exact I. (* new tactic *)
Qed.

(** The final tactic in that proof, [exact], can be used whenever you already
know exactly the program expression you want to write to provide evidence for
the goal you are trying to prove.  In this case, we know that [I] always
provides evidence for [true].  Instead of [exact] we could also have used
[trivial], which is capable of proving trivial propositions like [True]. *)

(**********************************************************************)

(** Negation *)

Locate "~".
Print not.

(**
Coq responds
<<
not = fun A : Prop => A -> False
     : Prop -> Prop
>>

  + Unlike "/\" and "\/" negation is a function not an inductive type.
  + [~P] is effectively syntactic sugar for [P -> False].
*)

Theorem notFalse : ~False -> True.
(** Intuition:  anything implies [True] *)
Proof.
  unfold not. (* new tactic *)
  intros.
  exact I.
Qed.

Print notFalse.
(* Ignores the argument *)

Theorem notTrue: ~True -> False.
Proof.
  unfold not. 
  intros t_imp_f. 
  apply t_imp_f. 
  exact I.
Qed.

(** The program that proof produces is interesting: *)

Print notTrue.

(**
Coq responds
<<
notTrue = fun t_imp_f : True -> False => t_imp_f I
     : ~ True -> False
>>

* Proof is a higher-order function
  + Takes [t_imp_f] function and uses [I] to get the proof for [False]
* We can never apply this function
  + cannot produce a term that returns [False]
*)

Theorem contra_implies_anything : forall (P Q : Prop), P /\ ~P -> Q.
(** Intuition:  principle of explosion *)
Proof.
    unfold not.
    intros. 
    destruct H.
    contradiction. (* detects contradiction *)
Qed.

(**********************************************************************)

(** deMorgan's laws *)


Theorem deMorgan : forall P Q : Prop,
  ~(P \/ Q) -> ~P /\ ~Q.

(** Intuition: if evidence for [P] or [Q] would lead to an explosion (i.e.,
   [False]), then evidence for [P] would lead to an explosion, and evidence 
   for [Q] would also lead to an explosion. *)
   
Proof.
  unfold not.
  intros P Q PorQ_imp_false.
  split.
  - intros P_holds. apply PorQ_imp_false. left. assumption.
  - intros Q_holds. apply PorQ_imp_false. right. assumption.
Qed.

(* Something interesting happens here *)
Theorem deMorgan2 : forall P Q : Prop,
  ~(P /\ Q) -> ~P \/ ~Q.
Proof.
  unfold not.
  intros P Q PQ_imp_false.
  left.
  intros P_holds. apply PQ_imp_false. split. assumption.
Abort.
(* stuck! *)

(** There's no reason that 
      "if evidence for P and Q would produce an explosion" 
         implies 
      "either evidence for P would produce an explosion, or evidence for Q would". 
      
    + It's the combined evidence for [P] and [Q] that produces the explosion  
    + nothing is said about evidence for them individually.
    + Coq uses _Constructive logic_; [deMorgan2] holds in _classical logic_
*)

Theorem excluded_middle : forall P, P \/ ~P.
Proof.
  intros P.
  left.
Abort.

(* Coq uses constructive logic since the act of proving programs is by building evidence bottom up. No bottom up evidence for [P \/ ~P]. *) 

Require Coq.Logic.Classical.

Module LetsDoClassicalReasoning.

Import Coq.Logic.Classical.

Print classic.

(**
Coq responds:
<<
*** [ classic : forall P : Prop, P \/ ~ P ]
>>

The [***] indicates that [classic] is an _axiom_ that the library simply asserts without proof.  Using that axiom, all the usual theorems of classical logic can be proved, such as double negation: *)


End LetsDoClassicalReasoning.

(**********************************************************************)

(** Equality and implication *)

Locate "=".
Print eq.
(* Takes a type [A] and argument [x], returns a function of type [A -> Prop]. *)

Definition eq42 := @eq nat 42.
Check eq42.
Check (eq42 42).
Check (eq42 43).

(* There's only one way to construct a value of type [eq],
     that's with the [eq_refl] constructor. *)

Check @eq_refl.
Check @eq_refl nat 42.
(* 
  + [@eq_refl] only takes just a single argument of type [nat]
    * An argument can only be equal to itself
  + Takeaway: Equality not baked into Coq, but an inductive type.
*)

Theorem direct_eq : 42 = 42.
Proof.
  exact (eq_refl 42). 
Qed.

(** Implication too is defined. *)

Locate "->".

(**
Coq responds:
<<
"A -> B" := forall _ : A, B 
>>

A function that takes the evidence for [A] and produces evidence for [B]. *)

Definition pnqiq : forall P Q, P /\ Q -> Q := fun P Q pnq =>
  match pnq with
  | conj evP evQ => evQ
  end.
  
Definition pnqiq' : forall P Q, forall (_: P /\ Q), Q := pnqiq.


(**

+ Only truly primitive pieces are [Inductive] definitions and [forall] types. 
   + Everything else --- equality, implication, conjunction, disjunction, true, false,
negation --- can all be expressed in terms of those two primitives.
*)