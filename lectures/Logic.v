(** 
* Logic in Coq
  
  From: https://www.cs.cornell.edu/courses/cs3110/2018sp/l/20-coq-logic/notes.v 
-----
#<i>#
Topics:

- propositions and proofs
- [Prop] and [Set]
- propositional logic
- implication
- conjunction
- disjunction
- [False] and [True]
- negation
- equality and implication revisited
- tautologies

#</i>#

-----

(**********************************************************************)


** Propositions and proofs

Recall that the [Check] command type checks an expression and causes Coq
to output the type in the output window. 
*)

Check list.

(** The type of [list] is [Type -> Type].  It takes a type as input and produces
a type as output.  Thus, like OCaml's [list], Coq's [list] is a type
constructor. But unlike OCaml, the type of Coq's [list] contains [->],
indicating that it is a function.  In Coq, [list] truly is a function that can
be applied: *)

Definition natlist : Type := list nat.
Check natlist.

(**
Think of Coq's [list] as a _type-level function_:  it is a function that takes
types as inputs and produces types as outputs.  OCaml doesn't have anything
exactly equivalent to that.  

What, then, is the type of a theorem?
*)

Theorem obvious_fact : 1 + 1 = 2.
Proof. trivial. Qed.
Check obvious_fact.

(**
Coq responds:
<<
obvious_fact : 1 + 1 = 2
>>

So the type of [obvious_fact] is [1 + 1 = 2].  That might seem rather
mysterious. After all, [1 + 1 = 2] is definitely not an OCaml type.  But Coq's
type system is far richer than OCaml's.  In OCaml, we could think of [42 : int]
as meaning that [42] is a _meaningful_ expression of type [int].  There are
likewise _meaningless_ expressions---for example, [42+true] is meaningless in
OCaml, and it therefore cannot be given a type.  The meaning of [int] in OCaml
is that of a computation producing a value that fits within 2^63 bits and can be
interpreted as an element of Z, the mathematical set of integers.  

So what are meaningful Coq expressions of type [1 + 2 = 2]?  They are the
_proofs_ of [1 + 1 = 2].  There might be many such proofs; here are two: 

- reduce [1+1] to [2], then note that [x=x]. 

- subtract [1] from both sides, resulting in [1 + 1 - 1 = 2 - 1], reduce both 
  sides to [1], then note that [x = x]. 

Regardless of the exact proof, it is an _argument_ for, or _evidence_ for, the
assertion that [1 + 1 = 2].  So when we say that [obvious_fact : 1 + 1 = 2],
what we're really saying is that [obvious_fact] is a proof of [1 + 1 = 2].

Likewise, when we write [Definition x := 42.] in Coq, and then observe that [x :
nat], what we're saying is not just that [x] has type [nat], but also that there
is _evidence_ for the type [nat], i.e., that there do exist values of that type.
Many of them, in fact---just like there are many proofs of [1 + 1 = 2].

So now we have an explanation for what the type of [obvious_fact] is. But what
is its value?  Let's ask Coq.
*)

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
That is, [eq_refl] has type [x = x].  In other words, [eq_refl] asserts
something is always equal to itself, a property known as the _reflexivity of
equality_.

So the proof of [1 + 1 = 2] in Coq is really just that equality
is reflexive.  It turns out that Coq evaluates expressions before applying that
fact, so it evaluates [1+1] to [2], resulting in [2 = 2], which holds by
reflexivity.  Thus the proof we found above, using the [trivial] tactic,
corresponds to the first of the two possible proofs we sketched.
*)

(**********************************************************************)

(**
** [Prop] and [Set]

We've now seen that there are programs and proofs in Coq.  Let's investigate
their types.  We already know that [42], a program, has type [nat], and that
[eq_refl : 1 + 1 = 2].  But let's now investigate what the types of [nat] and [1
+ 1 = 2] are.  First, [nat]:
*)

Check nat.

(**
Coq says that [nat : Set].  Here, [Set] is a predefined keyword in Coq that we
can think of as meaning all program data types.  Further, we can ask what the
type of [Set] is:
*)

Check Set.

(** 
Coq says that [Set : Type], so [Set] is a type.  The Coq documentation
describes [Set] as being the type of _program specifications_, which describe
computations.  For example, 

- [42] specifies a computation that simply returns [42].  It's a specification
  because [42 : nat] and [nat : Set].

- [fun x:nat => x+1] specifies a computation that increments a natural number.
  It's a specification because it has type [nat -> nat], and [nat -> nat : Set].

- We could also write more complicated specifications to express computations
  such as list sorting functions, or binary search tree lookups.

Next, let's investigate what the type of [1 + 1 = 2] is.
*)

Check 1 + 1 = 2.

(**
Coq says that [1 + 1 = 2 : Prop].  This is the type of _propositions_, which are
logical formulas that we can attempt to prove.  Note that propositions are not
necessarily provable though. For example, [2110 = 3110] has type [Prop], even
though it obviously does not hold. What is the type of [Prop]?
*)

Check Prop.

(**
Coq says that [Prop : Type].  So [Prop] is also a type.  So far we have seen one
way of creating a proposition, by using the equality operator.  We could attempt
to learn more about that operator with [Check =.], but that will result in an
error:  [Check] doesn't work on this kind of notation, and there isn't something
like in OCaml where we can wrap an operator in parentheses.  Instead, we need to
find out what function name that operator corresponds to.  The command for that
is [Locate].
*)

Locate "=".

(**
Coq tells us two possible meanings for [=], and the second is what we want: 
<<
"x = y" := eq x y
>>
That means that anywhere [x = y] appears, Coq understands it as the function
[eq] applied to [x] and [y].  Now that we know the name of that function, we can
check it:
*)

Check eq.

(**
The output of that is a bit mysterious because of the [?A] that shows up in it.
What's going on is that [eq] has an implicit type argument.  (Implicit arguments
were discussed in the previous set of notes.)  If we prefix [eq] with [@] to
treat the argument as explicit, we can get more readable output.
*)

Check @eq.

(**
Coq says that 
<<
@eq : forall A : Type, A -> A -> Prop
>>
In other words, [@eq] takes a type argument [A], a value of type [A], another
value of type [A], and returns a proposition, which is the proposition asserting
the equality of those two values. So:

- [@eq nat 42 42] asserts the equality of [42] and [42], i.e., [42 = 42].  So 
  does [eq 42 42], where [nat] is implicit.

- [@eq nat 2110 3110] asserts the equality of [2110] and [3110].  
  So does [eq 2110 3110] and [2110=3110].  Of course they aren't equal, but
  we're still allowed to form such a proposition, even if it isn't provable.

- [@eq (nat->nat) (fun x => x+1) (fun n => 1+n)] asserts the equality of two 
  syntactically different increment functions, as does [eq (fun x => x+1) 
  (fun n => 1+n)] and [(fun x => x+1) = (fun x => 1+n)].

*)

(**********************************************************************)

(**
** Propositional logic

The standard propositional logic _connectives_ (ways of syntactically connecting
propositions together) are:

- Implication: [P -> Q].  In English we usually express this connective as 
   "if [P], then [Q]" or "P implies Q".

- Conjunction: [P /\ Q].  In English we usually express this connective as
  "P and Q".

- Disjunction: [P \/ Q].  In English we usually express this connective as
  "P or Q".  Keep in mind that this is the sense of the word "or" that
  allows one or both of [P] and [Q] to hold, rather than exactly one.

- Negation: [~P].  In English we usually express this connective as
  "not P".

All of these are ways of creating propositions in Coq.  Implication is so
primitive that it's simply "baked in" to Coq.  But the other connectives are
defined as part of Coq's standard library under the very natural names of [and],
[or], and [not].

In addition to those connectives, there are two propositions [True] and
[False] which always and never hold, respectively.  And we can have
variables representing propositions.  Idiomatically, we usually choose
names like [P], [Q], [R], ... for those variables.
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
Both [and] and [or] take two propositions as input and return a proposition;
[not] takes one proposition as input and returns a proposition.

At this point, you might have noticed that [->] seems to be overloaded:

- [t1 -> t2] is the type of functions that take an input of type [t1] and 
  return an output of type [t2].

- [P -> Q] is an proposition that asserts [P] implies [Q].

There is a uniform way to think about both uses of [->], which is as a
_transformer_.  A function of type [t1 -> t2] transforms a value of type [t1]
into a value of type [t2].  An implication [P -> Q] in a way transforms [P] into
[Q]: if [P] holds, then [Q] also holds; or better yet, a proof of [P -> Q] can 
be thought of as a function that transforms evidence for [P] into evidence for 
[Q].

Let's do some proofs with these connectives to get a better sense of
how they work.

(**********************************************************************)

** Implication

Let's try one of the simplest possible theorems we could prove using
implication:  P implies P.
*)

Theorem p_implies_p : forall P:Prop, P -> P.

(** 
That proposition says that for any proposition [P], it holds that [P] implies
[P].

Intuitively, why should be able able to prove this proposition?  That is, what
is an argument you could give to another human?  We always encourage you to try
to answer that question before launching into a Coq proof---for the same reason
your introductory programming instructor always encouraged you to think about
programs before you begin typing them.

So why does this proposition hold?  It's rather trivial, really.  If [P] holds,
then certainly [P] holds.  That is, [P] implies itself. An example in English
could be "if 6225 is fun, then 6225 is fun." If you've already assumed [P], then
necessarily [P] follows from your assumptions:  that's what it means to be an
assumption.  

The Coq proof below uses that reasoning. 
*)

Proof.
    intros P. 
    intros P_assumed. 
    assumption.
Qed.

(** The second step, [intros P_assumed], is a new use for the [intros] tactic.
This usage peels off the left-hand side of an implication and puts it into the
proof assumptions.  The third step, [assumption] is a new tactic. It finishes a
proof of a subgoal [G] whenever [G] is already an assumption in the proof. 

Let's look at the type of [p_implies_p].
*)

Check p_implies_p.

(**
Coq says [p_implies_p : forall P : Prop, P -> P].  So [p_implies_p] is proof
of, or evidence for, [forall P : Prop, P -> P], as we discussed above.
What is that evidence?  We can use [Print] to find out:
*)

Print p_implies_p.

(** 
Coq responds
<<
p_implies_p = 
fun (P : Prop) (P_assumed : P) => P_assumed
     : forall P : Prop, P -> P
>>

Let's pull that apart.  Coq says that [p_implies_p] is a name that is 
bound to a value and has a type.  The type we already know.  The value
is perhaps surprising:  it is a function!  Actually, maybe it shouldn't
be surprising given the discussion we had above about transformers.
[P -> P] should transform evidence for [P] into evidence for [P].  Trivially,
evidence for [P] already _is_ evidence for [P], so there's nothing to be done.
And we can see that in the function itself:

- it takes in an argument named [P], which is the proposition; and

- it takes in another argument named [P_assumed] of type [P].  Since
  [P_assumed] has a proposition as type, [P_assumed] must be evidence
  for that proposition.

- the function simply returns [P_assumed].  That is, it returns the
  evidence for [P] that was already passed into it as an argument.

Note that the names of the arguments to that function are the names
that we chose with the [intros] tactic.  

Let's clarify a subtle piece of terminology, "proof".  The proof of
[forall P:Prop, P -> P] is the anonymous function [fun (P : Prop) 
(P_assumed : P) => P_assumed ].  That is, the proof of a proposition
[P] is a program that has type [P].  On the other hand, the commands
we used above
<<
Proof.
    intros P. 
    intros P_assumed. 
    assumption.
Qed.
>>
are how we help Coq find that proof.  We provide guidance using tactics,
and Coq uses those tactics to figure out how to construct the program.
So although it's tempting to refer to [intros P. intros P_assumed.
assumption.] as the "proof"---and we often will as a kind of shorthand
terminology---the proof is really the program that is constructed, not
the tactics that help do the construction.

It is, by the way, possible to just directly tell Coq what the proof is
by using the command [Definition]:
*)

Definition p_implies_p_direct : forall P:Prop, P -> P := 
  fun p ev_p => ev_p.

(**
But rarely do we directly write down proofs, because for most propositions
they are not so trivial.  Tactics are a huge help in constructing
complicated proofs.

Let's try another theorem.  A _syllogism_ is a classical form of argument
that typically goes something like this:

- All humans are mortal.

- Socrates is a human.

- Therefore Socrates is mortal.

The first assumption in that proof, "all humans are mortal", is an implication:
if X is a human, then X is mortal.  The second assumption is that
Socrates is a human.  Putting those two assumptions together, we conclude
that Socrates is mortal.

We can formalize that kind of reasoning as follows:
*)

Theorem syllogism : forall P Q : Prop, 
  (P -> Q) -> P -> Q.

(**
How would you convince a human that this theorem holds?  By the same
reasoning as above.  Assume that [P -> Q].  Also assume [P].  Since
[P] holds, and since [P] implies [Q], we know that [Q] must also hold.

The Coq proof below uses that style of argument.
*)

Proof.
  intros P Q evPimpQ evP.
  apply evPimpQ. 
  assumption.
Qed.

(** 
The first line of the proof, [intros P Q evPimpQ evP] introduces four
assumptions.  The first two are the variables [P] and [Q]. The third is [P->Q],
which we give the name [evPimpQ] as a human-readable hint that it is evidence
that [P] implies [Q]. The fourth is [P], which we give the name [evP] as a hint
that we have assumed we have evidence for [P]. 

The second line of the proof, [apply evPimpQ], uses a new tactic [apply] to
apply the evidence that [P -> Q] to the goal of the proof, which is [Q].  This
transforms the goal to be [P].  Think of this as _backward reasoning_:  we know
we want to show [Q], and since we have evidence that [P -> Q], we can work
backward to conclude that if we could only show [P], then we'd be done.  

The third line concludes by pointing out to Coq that in fact we do
already have evidence for [P] as an assumption.

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

Picking that apart, [syllogism] is a function that takes four arguments.
The third argument [evPimpQ] is of type [P -> Q].  Going back to our reading
of [->] in different ways, we can think of [evPimpQ] as 

- a function that transforms something of type [P] into something of type [Q],
  or

- evidence for [P -> Q],
  or

- a transformer that takes in evidence of [P] and produces evidence of [Q].

The deep point here is:  _all of these are really the same interpretation_.
There's no difference between them.  The value [evPimpQ] is a function, 
and it is evidence, and it is an evidence transformer.  

We can see that [evPimpQ] is being used as a function in the body 
[evPimpQ evP] of the anonymous function, above.  It is applied to
[evP], which is the evidence for [P], thus producing evidence for [Q].
So "apply" really is a great name for the tactic:  it causes a function
application to occur in the proof.

Let's try one more proof with implication.
*)

Theorem imp_trans : forall P Q R : Prop,
  (P -> Q) -> (Q -> R) -> (P -> R).

(**
As usual, let's first try to give an argument in English.  We assume
that [P -> Q] and [Q -> R], and we want to conclude [P -> R].  So suppose
that [P] did hold.  Then from [P -> Q] we'd conclude [Q], and then from
[Q -> R] we'd conclude [R].  So there's a kind of chain of evidence here
from [P] to [Q] to [R].  This kind of chained relationship is called
_transitive_, as you'll recall from CS 2800.  So what we're proving
here is that implication is transitive, hence the name [imp_trans]. 
*)

Proof.
  intros P Q R evPimpQ evQimpR.
  intros evP.
  apply evQimpR.
  apply evPimpQ.
  assumption.
Qed.

(**
The second line, [intros evP], wouldn't actually need to be separated
from the first line; we could have introduced [evP] along with the rest.
We did it separately just so that we could see that it peels off the
[P] from [P -> R].

The third line, [apply evQimpR] applies the evidence that [Q -> R] to
the goal [R], causing the goal to become [Q].  Again, this is backward
reasoning:  we want to show [R], and we know that [Q -> R], so if 
we could just show [Q] we'd be done.  

The fourth line, [apply evPimpQ], applies the evidence that [P -> Q]
to the goal [Q], causing the goal to become [P].

Finally, the fifth line, [assumption], finishes the proof by pointing
out that [P] is already an assumption.

Let's look at the resulting proof:
*)

Print imp_trans.

(**
Coq says
<<
imp_trans = 
fun (P Q R : Prop) (evPimpQ : P -> Q) (evQimpR : Q -> R) (evP : P) =>
evQimpR (evPimpQ evP)
     : forall P Q R : Prop, (P -> Q) -> (Q -> R) -> P -> R
>>

Drilling down into the body of that anonymous function we see
[evQimpR (evPimpQ evP)].  So we have [evPimpQ] being applied to [evP], which
transforms the evidence for [P] into the evidence for [Q].  Then we have
[evQimpR] applied to that evidence for [Q], thus producing evidence for [R].  So
there are two function applications.  If Coq had the OCaml operator [|>], we
could rewrite that function body as [evP |> evPimpQ |> evQimpR], which might
make it even clearer what is going on:  the chain of reasoning just takes [P] to
[Q] to [R].

(**********************************************************************)

** Conjunction

Now we turn our attention to the conjunction connective.  Here's
a first theorem to prove.
*)

Theorem and_fst : forall P Q, P /\ Q -> P.

(** Why does that hold, intuitively?  Suppose we have evidence for [P /\ Q].
Then we must have evidence for both [P] and for [Q]. The evidence for [P] alone
suffices to conclude [P].  As an example, if we have evidence that [x > 0 /\ y >
0], then we must have evidence that [x > 0]; we're allowed to forget about the
evidence for [y > 0].

Having established that intuition, let's create a proof with Coq.
*)

Proof. 
    intros P Q PandQ.
    destruct PandQ as [P_holds Q_holds]. 
    assumption.
Qed.

(**
The second line of that proof uses a familiar tactic in a new way.
Previously we used [destruct] to do case analysis, splitting apart
a [day] into the seven possible constructors it could have.
Here, we use [destruct] to split the evidence for [P /\ Q] into
its separate components.  To give names to those two components,
we use a new syntax, [as [...]], where the names appearing in 
the [...] are used as the names for the components.  If we leave
off the [as] clause, Coq will happily choose names for us, but
they won't be human-readable, descriptive names.  So it's good
style to pick the names ourselves.  

After destructing the evidence for [PandQ] into evidence for
[P] and evidence for [Q], we can easily finish the proof
with [assumption].

Let's look at the proof of [and_fst].
*)

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

Let's dissect that.  We see that [and_fst] is a function that takes three
arguments.  The third is evidence for [P /\ Q].  The function then pattern
matches against that evidence, providing just a single branch in the pattern
match.  The pattern it uses is [conj P_holds _].  As in OCaml, [_] is a wildcard
that matches anything.  The identifier [conj] is a constructor; unlike OCaml,
it's fine for constructors to begin with lowercase characters.  So the pattern
matches against [conj] applied to two values, extracts the first value with the
name [P_holds], and doesn't give a name to the second value.  The branch then
returns that argument [P_holds].  So we can already see that the function is
splitting apart the evidence into two pieces, and forgetting about one piece.

But to fully understand this, we need to know more about [/\] and [conj].
First, what is [/\]?
*)

Locate "/\".

(**
Coq says ["A /\ B" := and A B].  That is, [/\] is just an infix notation
for the [and] function.  What is [and]?
*)

Print and.

(**
Coq says
<<
Inductive and (A B : Prop) : Prop :=  
  conj : A -> B -> A /\ B
>>

It might help to compare to lists.
*)

Print list.

(**
Coq says
<<
Inductive list (A : Type) : Type :=
    nil : list A | cons : A -> list A -> list A
>>

In Coq, [Inductive] defines a so-called _inductive_ type, and provides its
constructors.  In OCaml, the [type] keyword serves a similar purpose. So [list]
in Coq is a type with two constructors named [nil] and [cons]. Similarly, [and]
is a type with a single constructor named [conj], which is a function that takes
in a value of type [A], a value of type [B], and returns a value of type [A /\
B], which is just infix notation for [and A B].  Another way of putting that is
that [conj] takes in evidence of [A], evidence of [B], and returns evidence of
[and A B].  

So there's only one way of producing evidence of [A /\ B], which is to
separately produce evidence of [A] and of [B], both of which are passed into
[conj].  That's why when we destructed [A /\ B], it had to produce both evidence
of [A] and of [B]. 

Going back to [and_fst]:
<<
and_fst = 
fun (P Q : Prop) (PandQ : P /\ Q) =>
match PandQ with
| conj P_holds _ => P_holds
end
     : forall P Q : Prop, P /\ Q -> P
>>
we have a function that pattern matches against [PandQ], extracts the
evidence for [P], forgets about the evidence for [Q], and simply returns
the evidence for [P].

Given all that, the following theorem and its program should be
unsurprising.
*)

Theorem and_snd : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q PandQ.
  destruct PandQ as [P_holds Q_holds].
  assumption.
Qed.

Print and_snd.

(**
Coq responds:
<<
and_snd = 
fun (P Q : Prop) (PandQ : P /\ Q) =>
match PandQ with
| conj _ Q_holds => Q_holds
end
     : forall P Q : Prop, P /\ Q -> Q
>>

In that program the pattern match returns the second piece of evidence, which
shows [Q] holds, rather than the first, which would show that [P] holds.

Here is another proof involving [and]. *)

Theorem and_ex : 42=42 /\ 43=43.

(** Why does that hold, intuitively?  Because equality is reflexive, regardless
of how many times we connect that fact with [/\]. *)

Proof. 
  split. 
  trivial. trivial.
Qed.

(** The first line of that proof, [split], is a new tactic.  It splits a goal of
the form [P /\ Q] into two separate subgoals, one for [P], and another for [Q].
Both must be proved individually.  In the proof above, [trivial] suffices to
prove them, because they are both trivial equalitiies.

What is [and_ex]? *)

Print and_ex.

(**
Coq responds:
<<
and_ex = conj eq_refl eq_refl
     : 42 = 42 /\ 43 = 43
>>

So [and_ex] is [conj] applied to [eq_refl] as its first argument and [eq_refl]
as its second argument.

As another example of conjunction, let's prove that it is commutative. *)

Theorem and_comm: forall P Q, P /\ Q -> Q /\ P.

(**
Why does this hold?  If we assume that [P /\ Q] holds, then separately we must
have evidence for [P] as well as [Q]. But the we could just assemble that
evidence in the opposite order, producing evidence for [Q /\ P].  That's what
the proof below does.
*)

Proof.
    intros P Q PandQ. 
    destruct PandQ as [P_holds Q_holds]. 
    split. 
    all: assumption.
Qed.

(**
There's nothing new in that proof:  we split the evidence into two pieces using
pattern matching, then reassemble them in a different order.  We can see that in
the program:
*)

Print and_comm.

(**
Coq responds:
<<
and_comm = 
fun (P Q : Prop) (PandQ : P /\ Q) =>
match PandQ with
| conj P_holds Q_holds => conj Q_holds P_holds
end
     : forall P Q : Prop, P /\ Q -> Q /\ P
>>

Note how the pattern match binds two variables, then returns the [conj]
constructor applied to those variables in the opposite order.

Here's one more proof involving implication and conjunction. *)

Theorem and_to_imp : forall P Q R : Prop,
  (P /\ Q -> R) -> (P -> (Q -> R)).

(** Intuitively, why does this hold?  Because we can assume [P], [Q] and [R]. as
well as that [P /\ Q -> R], and that we have evidence for [P] and [Q] already.
We can combine those two pieces of evidence for [P] and [Q] into a single piece
of evidence for [P /\ Q], which then yields the desired evidence for [R]. *)

Proof.
  intros P Q R evPandQimpR evP evQ.
  apply evPandQimpR.
  split.
  all: assumption.
Qed.

(** There are no new tactics in the proof above.   In line 2, we use [apply] to
once again do backwards reasoning, transforming the goal of [R] into [P /\ Q].
Then we split that goal into two pieces, each of which can be solved by
assumption.

Let's look at the resulting program: *)

Print and_to_imp.

(**
<<
and_to_imp = 
fun (P Q R : Prop) (evPandQimpR : P /\ Q -> R) (evP : P) (evQ : Q) => 
      evPandQimpR (conj evP evQ)
  : forall P Q R : Prop, (P /\ Q -> R) -> P -> Q -> R
>>

That program constructs evidence for [P /\ Q] using [P] and [Q], and 
uses the evidence to get [R] from [P /\ Q].

(**********************************************************************)

** Disjunction

Let's start with disjunction by proving a theorem very similar to the first
theorem we proved for conjunction: *)

Theorem or_left : forall (P Q : Prop), P -> P \/ Q.

(** As always, what's the intuition?  Well, if we have evidence for [P], then we
have evidence for [P \/ Q], because we have evidence already for the left-hand
side of that connective.

Let's formalize that argument in Coq. *)

Proof.
    intros P Q P_holds. 
    left. 
    assumption.
Qed.

(** The second line of that proof, [left], uses a new tactic that tells Coq we
want to prove the left-hand side of a disjunction.  Specifically, the goal at
that point is [P \/ Q], and [left] tells Coq the throw out [Q] and just focus on
proving [P].  That's easy, because [P] is already an assumption.

Let's investigate the resulting program. *)

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
Print or_introl.

(**
We learn that "\/" is infix notation for [or A B], and
[or_introl] is one of two constructors of the type [or]:
<<
Inductive or (A B : Prop) : Prop :=
    or_introl : A -> A \/ B 
  | or_intror : B -> A \/ B
>>

Those constructors take evidence for either the left-hand side or right-hand
side of the disjuncation.  So the body of [or_left] is just taking evidence for
[A] and using [or_introl] to construct a value with that evidence.

Similarly, the following theorem constructs proof using evidence for the
right-hand side of a disjunction. *)

Theorem or_right : forall P Q : Prop, Q -> P \/ Q.

(** Much like with [or_left], this intuitively holds because evidence for [Q]
suffices as evidence for [P \/ Q]. *)

Proof. 
  intros P Q Q_holds.
  right.
  assumption.
Qed.

Print or_right.

(**
The resulting program uses the constructor [or_intror]:
<<
or_right = 
fun (P Q : Prop) (Q_holds : Q) => or_intror Q_holds
     : forall P Q : Prop, Q -> P \/ Q
>>

We could use those theorems to prove some related theorems.
For example, [3110 = 3110] implies that [3110 = 3110 \/ 2110 = 3110].
*)

Theorem or_thm : 3110 = 3110 \/ 2110 = 3110.

(**
Why does that hold?  Because the left-hand side holds---even though
the right hand side does not.
*)

Proof. 
  left. trivial.
Qed.

Print or_thm.

(**
Coq responds that
<<
or_thm = or_introl eq_refl
     : 3110 = 3110 \/ 2110 = 3110
>>

In other words, the theorem is proved by applying the [or_introl] constructor to
[eq_refl].  It matters, though, that we provided Coq with the guidance to prove
the left-hand side. If we had chosen the right-hand side, we would have been
stuck trying to prove that [2110 = 3110], which of course it does not.

Next, let's prove that disjunction is commutative, as we did for conjunction
above. *)


Theorem or_comm : forall P Q, P \/ Q -> Q \/ P.

(** Why does this hold?  If you assume you have evidence for [P \/ Q], then you
either have evidence for [P] or evidence for [Q]. If it's [P], then you can
prove [Q \/ P] by providing evidence for the right-hand side; or if it's [Q],
for the left-hand side.  

That's what the Coq proof below does. *)

Proof.
    intros P Q PorQ.
    destruct PorQ as [P_holds | Q_holds].
    - right. assumption.
    - left. assumption.
Qed. 

(** In the second line of that proof, we destruct the disjunction [PorQ] with a
slightly different syntax than when we destructed conjunction above.  There's
now a vertical bar.  The reason for that has to do with the definitions of [and]
and [or].  

The definition of [and] had just a single constructor:
<<
conj : A -> B -> A /\ B
>>
So when we wrote [destruct PandQ as [P_holds Q_holds]], we were essentially
writing a pattern match against that single constructor [conj], and binding its
[A] argument to the name [P_holds], and its [B] argument to the name [Q_holds].

But the definition of [or] has two constructors:
<<
    or_introl : A -> A \/ B 
  | or_intror : B -> A \/ B
>>
So when we write [destruct PorQ as [P_holds | Q_holds]], we're providing two
patterns: the first matches against the first constructor [or_introl], binding
its [A] argument to the name [P_holds]; and the second against the second
constructor [or_intror], binding its [B] argument to [Q_holds]. 

What makes this confusing to an OCaml programmer is that the [as] clause doesn't
actually name the constructors.  It might be clearer if Coq's [destruct] tactic
used the following hypothetical syntax:
<<
  destruct PandQ as [conj P_holds Q_holds].
  destruct PorQ as [or_introl P_holds | or_intror Q_holds].
>>
but that's just not how [destruct..as] works.

After the destruction occurs, we get two new subgoals to prove, corresponding to
whether [PorQ] matched [or_introl] or [or_intror]. In the third line of the
proof, which corresponds to [PorQ] matching [or_introl], we have evidence for
[P], so we choose to prove the right side of [Q \/ P] by assumption.  The fourth
line does a similar thing, but using evidence for [Q] hence proving the left
side of [Q \/ P].

Let's look at the resulting proof. *)

Print or_comm.

(**
Coq responds
<<
or_comm = 
fun (P Q : Prop) (PorQ : P \/ Q) =>
match PorQ with
| or_introl P_holds => or_intror P_holds
| or_intror Q_holds => or_introl Q_holds
end
     : forall P Q : Prop, P \/ Q -> Q \/ P)
>>

That function takes an argument [PorQ] is evidence for [P \/ Q], pattern matches
against that argument, extracts the evidence for either [P] or [Q], then returns
that evidence wrapped in the "opposite" constructor:  evidence that came in in
the left constructor is returned with the right constructor, and vice versa.  

Next, let's prove a theorem involving both conjunction and disjunction. *)


Theorem or_distr_and : forall P Q R, 
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).

(** This theorem says that "or" distributes over "and".  Intuitively, if we have
evidence for [P \/ (Q /\ R)], then one of two things holds: either we have
evidence for [P], or we have evidence for [Q /\ R].

- If we have evidence for [P], then we use that evidence to create evidence both
  for [P \/ Q] and for [P /\ R].

- If we have evidence for [Q /\ R], then we split that evidence apart into
  evidence separately for [Q] and for [R].  We use the evidence for
  [Q] to create evidence for [P \/ Q], and likewise the evidence for [R] to
  create evidence for [P \/ R].

The Coq proof below follows that intuition. *)

Proof.
  intros P Q R PorQR.
  destruct PorQR as [P_holds | QR_holds].
  - split.
    + left. assumption.
    + left. assumption.
  - destruct QR_holds as [Q_holds R_holds].
    split.
    + right. assumption.
    + right. assumption.
Qed.

(** We used _nested bullets_ in that proof to keep the structure of the proof
clear to the reader, and to make it easier to follow the proof in the proof
window when we step through it.  

But you'll notice there's a lot of repetition in the proof.  We can eliminate
some by using the [;] tactical (discussed in the previous notes) to chain
together some proof steps. *)

Theorem or_distr_and_shorter : forall P Q R, 
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R PorQR.
  destruct PorQR as [P_holds | QR_holds].
  - split; left; assumption.
  - destruct QR_holds as [Q_holds R_holds].
    split; right; assumption.
Qed.

Print or_distr_and.

(**
Either way, the resulting proof is
<<
or_distr_and = 
fun (P Q R : Prop) (PorQR : P \/ Q /\ R) =>
match PorQR with
| or_introl P_holds => conj (or_introl P_holds) (or_introl P_holds)
| or_intror QR_holds =>
    match QR_holds with
    | conj Q_holds R_holds => conj (or_intror Q_holds) (or_intror R_holds)
    end
end
     : forall P Q R : Prop, P \/ Q /\ R -> (P \/ Q) /\ (P \/ R)
>>

The nested pattern match in that proof corresponds to the nested [destruct]
above.  Note that Coq omits some parentheses around conjunction, because it is
defined to have higher precedence than disjunction---just like [*] has higher
precedence than [+].

(**********************************************************************)

** [False] and [True]

[False] is the proposition that can never hold:  we can never actually have
evidence for it.  If we did somehow have evidence for [False], our entire system
of reasoning would be broken. There's a Latin phrase often used for that idea:
_ex falso quodlibet_, meaning "from false, anything".  In English it's sometimes
known as the _Principle of Explosion_:  if you're able to show [False], then
everything just explodes, and in fact anything at all becomes provable.

Here's the definition of [False]: *)

Print False.

(**
Coq responds
<<
Inductive False : Prop :=  
>>

No, that isn't a typo above.  There is nothing on the right-hand side of the
[:=].  The definition is saying that [False] is an inductive type, like [and]
and [or], but it has zero constructors.  Since it has no constructors, we can
never create a value of type [False]---and that means we can never create
evidence that [False] holds.  

Let's prove the Principle of Explosion. *)

Theorem explosion : forall P:Prop, False -> P.

(** Why should this theorem hold?  Because of the intuition we gave above
regarding _ex falso_. *)

Proof.
    intros P false_holds. 
    contradiction.
Qed.

(** The second line of the proof uses a new tactic, [contradiction].  This
tactic looks for any contradictions or assumptions of [False], and uses those to
conclude the proof.  In this case, it immediately finds [False] as an assumption
named [false_holds].*)

Print explosion.
Print False_ind.

(**
The proof that Coq finds for [explosion] given the above tactics is a little bit
hard to follow because it uses [False_ind] that are already defined for us.
Its definition is given below, but it's okay if you want to skip over reading 
them at first.

<<
explosion = 
fun (P : Prop) (false_holds : False) => False_ind P false_holds
     : forall P : Prop, False -> P

False_ind =
fun (P : Prop) (f : False) => match f return P with
                              end
     : forall P : Type, False -> P
>>

(The [return P] in the pattern match above is a type annotation: it says
that the return type of the entire [match] expression is [P].)

We could simplify the proof of [explosion] by just directly writing that pattern match ourselves.  Let's do that using the [Definition] command we saw above. 
*)

Definition explosion' : forall (P:Prop), False -> P := 
  fun (P : Prop) (f : False) => 
    match f with 
    end.

(** 
The proof of [explosion'] is a function that takes two inputs, a proposition
[P] and a value [f] of type [False].  As usual, we should understand that second
argument as being evidence for [False].  But it should be impossible to
construct such evidence!  And indeed it is, because [False] has no constructors.
So we have a function that we could never actually apply.

In the body of that function is a pattern match against [f].  That pattern match
has zero branches in it, exactly because [False] has zero constructors. There is
nothing that could ever possibly match [f].

The return type of the function is [P], meaning it purportedly is evidence for
[P].  But of course no such evidence is ever constructed by the function, nor
could it be.  So it's a good thing that it's impossible to apply the function.
Were it possible, it would have to fabricate evidence for any proposition [P]
whatsoever---which is not possible. 

We can never prove [P -> P /\ False], because there is no way to construct the
evidence for the right side. *)

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

(** [True] is the proposition that is always true, i.e., for which we can always
provide.  It is defined by Coq as an inductive type: *)

Print True.

(**
Coq responds:
<<
Inductive True : Prop :=  I : True
>>

So [True] has a single constructor [I], and anywhere we write [I], that provides
evidence for [True].  Let's redo the two theorem we just did for [False], but
with [True] in place of [False]. *)

Theorem p_imp_p_and_true : forall P:Prop, P -> P /\ True.
Proof.
  intros P P_holds. split. assumption. exact I.
Qed.

(** The final tactic in that proof, [exact], can be used whenever you already
know exactly the program expression you want to write to provide evidence for
the goal you are trying to prove.  In this case, we know that [I] always
provides evidence for [true].  Instead of [exact] we could also have used
[trivial], which is capable of proving trivial propositions like [True]. *)

Theorem p_imp_p_or_true : forall P:Prop, P -> P \/ True.
Proof.
  intros P P_holds. left. assumption.
Qed.

(**
(**********************************************************************)

** Negation

The negation connective can be the trickiest to work with in Coq.  Let's start
by seeing how it is defined. *)

Locate "~".
Print not.

(**
Coq responds
<<
not = fun A : Prop => A -> False
     : Prop -> Prop
>>

Unlike conjunction and disjunction, negation is defined as a function, rather
than an inductive type.  Anywhere we write [~P], it really means [not P], which
is [(fun A => A -> False) P], which reduces to [P -> False].  In short, [~P] 
is effectively syntactic sugar for [P -> False].  

Here are two proofs involving negation, so that we can get used to this
definition of it. *)

Theorem notFalse : ~False -> True.
(** Intuition:  anything implies [True], regardless of what that anything is. *)
Proof.
  unfold not.
  intros.
  exact I.
Qed.

(** The first line of that proof, [unfold not], is a new tactic, which replaces
the [~] in the goal with its definition and simplifies it.  So [~False] becomes
[False -> False]. The second line uses a familiar tactic in a new way. We don't
provide any names to [intros], which causes Coq to choose its own names.
Normally we consider it good style to choose them ourselves, but here, we don't
care what they are, because we are never going to use them.  Finally, the third
line uses [I] to prove [True].

Looking at the actual program produced, we see that it's very simple:
*)

Print notFalse.

(**
Coq responds
<<
notFalse = fun _ : False -> False => I
>>

which is a function that takes an argument that is never used, and simply
returns [I], which is the evidence for [True].

Here's a second proof involving negation. *)

Theorem notTrue: ~True -> False.
(** Intuition:  if [True] implies [False], and if [True], then [False]. *)
Proof.
  unfold not. 
  intros t_imp_f. 
  apply t_imp_f. 
  exact I.
Qed.

(** The first line of the proof replaces [~True] with [True -> False]. The rest
of the proof proceeds by moving [True -> False] into the assumptions, then
applying it to do backward reasoning, leaving us with needing to prove [True].
That holds by the [I] constructor.

The program that proof produces is interesting: *)

Print notTrue.

(**
Coq responds
<<
notTrue = fun t_imp_f : True -> False => t_imp_f I
     : ~ True -> False
>>

That proof is actually a higher-order function that takes in a function
[t_imp_f] and applies that function to [I], thus transforming evidence
for [True] into evidence for [False], and returning that evidence.  If
that seems impossible, it is!  We'll never be able to apply this function,
because we'll never be able to construct a value to pass to it whose
type is [~True], i.e., [True -> False].   

Next, let's return to the idea of explosion.  From a contradiction we should
be able to derive anything at all.  One kind of contradiction is for a 
proposition and its negation to hold simultaneously, e.g., [P /\ ~P].
*)

Theorem contra_implies_anything : forall (P Q : Prop), P /\ ~P -> Q.
(** Intuition:  principle of explosion *)
Proof.
    unfold not.
    intros P Q PandnotP. 
    destruct PandnotP as [P_holds notP_holds]. 
    contradiction.
Qed.

(** This proof proceeds along familiar lines:  We destruct the evidence of [P /\
~P] into two pieces.  That leaves us with [P] as an assumption as well as [~P].
The [contradiction] tactic detects those contradictory assumptions and finished
the proof.  By the way, we could have left out the [as] clause in the [destruct]
here, since we are never going to use the names we chose, but they will help
make the following program more readable: *)

Print contra_implies_anything.

(**
Coq responds:
<<
contra_implies_anything = 
fun (P Q : Prop) (PandnotP : P /\ (P -> False)) =>
match PandnotP with
| conj P_holds notP_holds => False_ind Q (notP_holds P_holds)
end
     : forall P Q : Prop, P /\ ~ P -> Q
>>

The really interesting part of this is the body of the pattern match,
[False_rect Q (notP_holds P_holds)].  It applies [notP_holds] to [P_holds], thus
transforming evidence for [P] into evidence for [False]. It passes that
hypothetical evidence for [False] to [False_ind], which as we've seen before
uses such evidence to produce evidence for anything at all that we would
like---in this case, [Q], its first argument.

Next, let's try a proof involving all the connectives we've seen: negation,
conjunction, disjunction, and implication.  The following theorem shows how
negation distributes over disjunction, and in so doing, produces a conjunction.
The name we choose for this theorem is traditional and gives credit to Augustus
De Morgan, a 19th century logician, even though the theorem was known far
earlier in history. *)

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

(** Nothing we've done in that proof is new, but it is longer than any of our
proofs so far.  The same is true of the program it produces: *)

Print deMorgan.

(**
Coq responds:
<<
deMorgan = 
fun (P Q : Prop) (PorQ_imp_false : P \/ Q -> False) =>
conj (fun P_holds : P => PorQ_imp_false (or_introl P_holds))
     (fun Q_holds : Q => PorQ_imp_false (or_intror Q_holds))
       : forall P Q : Prop, ~ (P \/ Q) -> ~ P /\ ~ Q
>>

There is a second "De Morgan's Law", which says that negation distributes over
conjunction, thus producing a disjunction.  But something seemingly goes very
wrong when we try to prove it in Coq: *)

Theorem deMorgan2 : forall P Q : Prop,
  ~(P /\ Q) -> ~P \/ ~Q.

(** Intuition: if evidence for P and Q would produce an explosion, then 
either evidence for P would produce an explosion, or evidence for Q would. *)

Proof.
  unfold not.
  intros P Q PQ_imp_false.
  left.
  intros P_holds. apply PQ_imp_false. split. assumption.
Abort.

(** When we get to the point in the proof above where we need to prove [Q], we
have no means to do so.  (The same problem would occur for [P] if instead of
[left] we had gone [right].)  Why does this happen?  One reason is that the
intuition we gave above is wrong!  There's no reason that "if evidence for P and
Q would produce an explosion" implies "either evidence for P would produce an
explosion, or evidence for Q would". It's the combined evidence for [P] and [Q]
that produces the explosion in that assumption---nothing is said about evidence
for them individually.

But a deeper reason is that this theorem simply doesn't hold in Coq's logic:
there isn't any way to prove it.  That might surprise you if you've studied some
logic before, and you were taught that both De Morgan laws are sound reasoning
principles.  Indeed they are in some logics, but not in others.

In _classical logic_, which is what you almost certainly would have studied
before (e.g., in CS 2800), we are permitted to think of every proposition as
having a _truth value_, which is either [True] or [False].  And one way to prove
a theorem is to construct a _truth table_ showing what truth value a proposition
has for any assignment of [True] or [False] to its variables. For example
(writing [T] and [F] as abbreviations):

<<
P  Q  ~(P/\Q) (~P \/ ~Q) (~(P/\Q) -> (~P \/ ~Q))
T  T  F       F          T
T  F  T       T          T
F  T  T       T          T
F  F  T       T          T
>>

For every possible assignment of truth values to [P] and [Q], we get that the
truth value of [~(P/\Q) -> (~P \/ ~Q)] is [True].  So in classical logic,
[~(P/\Q) -> (~P \/ ~Q)] is a theorem.

But Coq uses a different logic called _constructive logic_.  Constructive logic
is more convervative than classical logic, in that it always requires evidence
to be produced as part of a proof.  As we saw above when we tried to prove
[deMorgan2], there just isn't a way to construct evidence for [~P \/ ~Q] out of
evidence for [~(P/\Q)].  

There are many other propositions that are provable in classical logic but not
in constructive logic.  Another pair of such propositions involves _double
negation_:  [P -> ~~P] is provable in both logics, but [~~P -> P] is provable in
classical logic and not provable in constructive logic.  Let's try proving both
just to see what happens. 
*)

Theorem p_imp_nnp : forall P:Prop, P -> ~~P.

(** Intuition: ~~P is (P -> False) -> False.  So the theorem could be
   restated as P -> (P -> False) -> False.  That's really just a syllogism,
   with the first two arguments in the opposite order:
   - P implies False.
   - P holds.
   - Therefore False holds. *)
   
Proof.
  unfold not.  
  intros P evP evPimpFalse.
  apply evPimpFalse. 
  assumption.
Qed.

(** We could make that intuition even more apparent by proving a version of the
syllogism theorem with its first two arguments swapped: *)

Theorem syllogism' : forall P Q : Prop,
  P -> (P -> Q) -> Q.
Proof.
  intros P Q evP evPimpQ.
  apply evPimpQ.
  assumption.
Qed.

(** Now we use [syllogism'] to prove [P -> ~~P]: *)

Theorem p_imp_nnp' : forall P:Prop, P -> ~~P.
Proof.
  unfold not. intros P. apply syllogism'.
Qed.

(** In that proof, we have a new use for the [apply] tactic: we use it with the
name of a theorem we've already proved, because our goal is in fact that
theorem.  In the resulting program, we saw this indeed becomes an application of
the [syllogism'] function: *)

Print p_imp_nnp'.

(**
Coq responds:
<<
p_imp_nnp' = 
fun P : Prop => syllogism' P False
     : forall P : Prop, P -> ~ ~ P
>>

Now let's try the other direction for double negation:
*)

Theorem nnp_imp_p : forall P : Prop, ~~P -> P.
(* intuition: actually it doesn't hold *)
Proof.
  unfold not.
  intros P evNNP.
Abort.

(** Once we get past introducing assumptions in that proof, we're stuck. There's
nothing we can do with [(P -> False) -> False] to prove [P]. Why?  Because in
constructive logic, to prove [P], we must produce evidence for [P].  Nothing in
[(P -> False) -> False] gives us such evidence.  

That's very different from classical logic, where we could just construct a
truth table:

<<
P ~~P  (~~P -> P)
T T    T
F F    T
>>

Here's another even more brutally perplexing proposition that's provable in
classical logic but not in constructive logic.  It's called _excluded middle_,
because it says that every proposition or its negation must hold; there is no
"middle ground": *)

Theorem excluded_middle : forall P, P \/ ~P.
Proof.
  intros P.
  left.
Abort.

(** Whether we go left or right in the second step of that proof, we immediately
get stuck.  If we go left, Coq challenges us to construct evidence for [P], but
we don't have any.  If we go right, Coq challenges us to construct evidence for
[P -> False], but we don't have any. 

Yet in classical logic, excluded middle is easily proved by a truth table:
<<
P  ~P  (P \/ ~P)
T  F   T
F  T   T
>>

Why does Coq use constructive logic rather than classical logic?  The reason
goes back to why we started looking at Coq, namely, program verification.  We'd
like to be able to extract verified programs.  Well, there simply is no program
whose type is [P \/ ~P], because such a program would have to use either
[or_introl] or [or_intror] to construct its result, and it would have to
magically guess which one to use, then magically somehow produce the appropriate
evidence.  

Nonetheless, if all you want to do is reasoning in classical logic, and you
don't care about extracting verified programs, Coq does support that in a
library [Coq.Logic.Classical]. We'll load that library now in a nested [Module],
which restricts its influence just to that module so that we don't pollute the
rest of this file. *)

Require Coq.Logic.Classical.

Module LetsDoClassicalReasoning.

Import Coq.Logic.Classical.

Print classic.

(**
Coq responds:
<<
*** [ classic : forall P : Prop, P \/ ~ P ]
>>

The [***] indicates that [classic] is an _axiom_ that the library simply asserts
without proof.  Using that axiom, all the usual theorems of classical logic can
be proved, such as double negation: *)

Print NNPP.

(**
Coq responds:
<<
NNPP = 
fun (p : Prop) (H : (p -> False) -> False) =>
or_ind (fun H0 : p => H0) (fun NP : ~ p => False_ind p (H NP)) (classic p)
     : forall p : Prop, ~ ~ p -> p
>>

You can see on the last line that [NNPP] proves [~~p -> p], which we couldn't
prove above.  And you'll see that [classic] shows up in the program to magically
construct evidence of [p \/ ~p]. *)

End LetsDoClassicalReasoning.

(**
(**********************************************************************)

** Equality and implication

Let's return to the two connectives with which we started, equality and
implication.  Earlier we didn't explain them fully, but now we're equipped to
appreciate their definitions.

Recall how Coq defines equality:
*)

Locate "=".
Print eq.

(**
Coq responds:
<<
Inductive eq (A : Type) (x : A) : A -> Prop :=  
  eq_refl : x = x

For eq: Argument A is implicit ...
>>

Reading that carefully, we see that [eq] is parameterized on 

- a type [A], and

- a value [x] whose type is [A].

We also see that [A] is implicit, so let's use [@eq] from now on in our
discussion just to be clear about [A].

When we apply [@eq] to a type [A] and a value [x], we get back a function of
type [A -> Prop].  The idea is that function will take its argument, let's call
it [y], and construct the proposition that asserts that [x] and [y] are equal.
For example: *)

Definition eq42 := @eq nat 42.
Check eq42.
Check (eq42 42).
Check (eq42 43).

(**
<<
eq42 : nat -> Prop
eq42 42 : Prop
eq42 43 : Prop
>>

There's only one way to construct a value of type [eq], though, and that's with
the [eq_refl] constructor.  If we "desugar" the [=] notation, that constructor
has type [@eq A x x], where [x] must be of type [A]. *)

Check @eq_refl nat 42.

(** 
<<
@eq_refl nat 42 : 42 = 42
>>

Note how the constructor above takes just a single argument of type [nat], not
two arguments:  it will only ever show that argument is equal to itself, never
to anything else.  There's literally no way to write an expression using
[eq_refl] to construct evidence that (e.g.) [42] and [43] are equal. 

So instead of using [trivial], we could directly use [eq_refl] as a constructor
to prove equalities, much like we directly used [I] as a constructor to prove
[True] earlier in this file: *)

Theorem direct_eq : 42 = 42.
Proof.
  exact (eq_refl 42). 
Qed.

(** Equality, therefore, is not something that has to be "baked in" to Coq, but
rather something that is definable as an inductive type---much like [and] and
[or].

And now back to implication.  It, too, is defined. *)

Locate "->".

(**
Coq responds:
<<
"A -> B" := forall _ : A, B 
>>

That is, [A -> B] is really just syntactic sugar for [forall (_:A), B], where
we've added some parentheses for a little bit more clarity. Still, that
expression is tricky to read because of the wildcard in it. It might help if we
made [A] and [B] concrete, for example, if [A] is [P /\ Q] and [B] is [Q], where
[P] and [Q] are propositions. Then we could think of the type [forall (_ : P /\
Q), Q] as follows:

- [(_ : P /\ Q)] means an unnamed value of type [P /\ Q].  Using the evidence 
  interpretation we've been developing throughout this file, that value would be 
  evidence that [P /\ Q] holds.  It's unnamed because it's not used on the
  right-hand side.

- A value of type [Q] would be evidence for [Q].

- So a value of type [forall (_ : P /\ Q), Q] would be a "thing" that
  for any piece of evidence that [P /\ Q] holds can produce evidence
  that [Q] holds.

What is such a "thing"?  A function!  It transforms evidence for one proposition
into evidence for another proposition. *)

Definition pnqiq : forall P Q, P /\ Q -> Q := fun P Q pnq =>
  match pnq with
  | conj evP evQ => evQ
  end.
  
Definition pnqiq' : forall P Q, forall (_: P /\ Q), Q := pnqiq.

(** 
 You can also see this duality with familiar functions. For example, consider 
 the [is_zero] function that returns [true] if the given number is [0]. *)

Definition is_zero n :=
  match n with
  | 0 => true
  | _ => false
  end.

(**
 This function has the type [nat -> bool].
 *)

Definition is_zero' : nat -> bool := is_zero.

(** 
 Equivalently, we can also assign the type [forall (_:nat), bool] to the [is_zero]
 function. *)

Definition is_zero'' : forall (_:nat), bool := is_zero.

(**

So of all the logic we've coded up in Coq in this file, the only truly primitive
pieces are [Inductive] definitions and [forall] types. Everything
else---equality, implication, conjunction, disjunction, true, false,
negation---can all be expressed in terms of those two primitives.

And although we had to learn many tactics, every proof we constructed with them
was really just a program that used functions, application, and pattern
matching.

(**********************************************************************)

** Tautologies

(Or, "How to make the computer do your CS 2800 logic homework for you".)

We needed to learn the tactics and definitions above for the more complicated
proofs we will later want to do in Coq.  But if all you care about is proving
simple logical propositions, there's a tactic for that: [tauto].  It will
succeed in finding a proof of any propositional _tautology_, which is a formula
that must always hold regardless of the values of variables in it.

For example, one of the most complicated proofs we did above was De Morgan's
law.  Here it is in just one tactic: *)

Theorem deMorgan' : forall P Q : Prop,
  ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  tauto.
Qed.

Print deMorgan'.

(**
Coq responds:

<<
deMorgan' = 
fun (P Q : Prop) (H : ~ (P \/ Q)) =>
let H0 := (fun H0 : P => H (or_introl H0)) : P -> False in
let H1 := (fun H1 : Q => H (or_intror H1)) : Q -> False in
conj (fun H2 : P => let H3 := H0 H2 : False in False_ind False H3)
  (fun H2 : Q => let H3 := H1 H2 : False in False_ind False H3)
     : forall P Q : Prop, ~ (P \/ Q) -> ~ P /\ ~ Q
>>

That's a bit more complicated of a proof than the one we constructed ourselves,
mainly because of the [let] expressions, but it still is correct. 

So if your CS 2800 prof wants you to prove a propositional tautology, and if
it's a proposition that holds in constructive logic, Coq's got your back: just
use [tauto] to do it.  

But don't tell your 2800 prof I told you that.

** Summary

Coq's built-in logic is constructive:  it isn't sufficient to argue that
a proposition must be true or false; rather, we have to construct evidence
for the proposition.  Programs are how we construct and transform evidence.
All of the propositional connectives, except implication, are "coded up"
in Coq using inductive types, and proofs about them routinely use pattern
matching and function application.

** Terms and concepts

- assumption
- classical logic
- conjunction
- constructive logic
- constructor
- contradiction
- De Morgan's laws
- disjunction
- double negation
- evidence
- excluded middle
- implication
- inductive type
- negation
- Principle of Explosion
- [Prop]
- proposition
- reflexivity
- [Set]
- syllogism
- tautology
- transitivity
- truth table

** Tactics

- [apply]
- [assumption]
- [contradiction]
- [destruct..as]
- [exact]
- [left]
- [right]
- [split]
- [tauto]
- tacticals: nested bullets [-], [*], [+]

** Further reading

- _Software Foundations, Volume 1: Logical Foundations_. 
  #<a href="https://softwarefoundations.cis.upenn.edu/lf-current/Logic.html">
  Chapter 6: Logic.</a>#

- _Interactive Theorem Proving and Program Development_.
  Chapters 5 and 8.2. Available 
  #<a href="https://newcatalog.library.cornell.edu/catalog/10131206">
  online from the Cornell library</a>#.

*)
