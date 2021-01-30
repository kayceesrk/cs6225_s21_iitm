(**
 
* Functional Programming in Coq

  From: https://www.cs.cornell.edu/courses/cs3110/2018sp/l/19-coq-fp/notes.v

-----
#<i>#
Topics:

- types and functions
- theorems and proofs
- lists
- options
#</i>#

-----

_Mega super hyper serious tip_:  You absolutely must step through this file
interactively in Coq to understand what's going on.  Observe what happens
to the proof state and in the output window.  Just reading this file
in your browser does not suffice!

(**********************************************************************)


** Types and functions

Let's start by doing some basic functional programming in Coq.
We'll define a type which represents the days of the week.
*)

Inductive day : Type :=
| sun : day
| mon : day
| tue : day
| wed : day
| thu : day
| fri : day
| sat : day.

(**

You'll note some differences from OCaml:

- The definition starts with the keyword [Inductive] instead of the keyword
  [type].

- [day] has a type itself, [Type].  Essentially this is saying that [day] is a
  type.

- The definition uses [:=] instead of [=].

- Every constructor is explicitly given the type [day]. Later we'll see that
  constructors can have more complicated types.

- The definition must end with a period.
*)

(**
Here's a function that returns the next day after its input.
*)


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

(**
Again, there are some small differences from OCaml:

- The [Let] keyword is capitalized.

- The pattern match must end with the [end] keyword.

- The branches use [=>] instead of [->] to separate the pattern from the value
  to be returned.

Although we can use [Let] in Coq, it's usually more idiomatic to write
[Definition] instead, because [Let] is actually substituted away.
We could instead write the following:
*)

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

(**********************************************************************)


(**

** Theorems and proofs

Now let's prove some small theorems about programs that use days.

First, let's prove that applying [next_day] to [tue] evaluates to [wed].
If you were going to do that with a more informal proof in natural
language, your first instinct might be to say "it's obvious."  That's
kind of what the proof below does.
*)

Theorem wed_after_tue : next_day tue = wed.
Proof.
  auto.
Qed.

(** [auto] is a _tactic_ that searches for a proof. Tactics are the commands
written between [Proof] and [Qed]; they manipulate the _proof state_, which is
all the _subgoals_ that need to be proved before the proof is finished.  We can
see the proof [auto] found by printing the theorem: *)

Print wed_after_tue.

(** The output of that is [wed_after_tue = eq_refl : next_day tue = wed], which
indicates that [wed_after_tue] is equal to [eq_refl] and proves that [next_day
tue = wed]. Here, [eq_refl] is something from the Coq standard library that says
equality is _reflexive_, and that computation may be performed on either side of
the equality to reduce the expression that appears there to a simpler
expression. *)

(** Rarely, though, is a theorem so simple that it can immediately be proved by
searching for a proof. Usually we need to provide Coq with more explicit
guidance. A more careful informal proof of the theorem might read "[next_day
tue] evaluates to [wed].  So the equality to be proved reduces to [wed = wed].
That trivially holds."  That is essentially the proof that strategy that is
followed below: *)

Theorem wed_after_tue' : next_day tue = wed.
Proof.
  simpl. trivial.
Qed.

(** Printing the theorem shows that it's still the same proof that is found by
[auto]. *)

Print wed_after_tue'.

(**
The output of that is [wed_after_tue' = eq_refl : next_day tue = wed].
*)

(** Next, let's prove that the day of the week never repeats.  That is, the day
after a given day [d] is never equal to [d]. *)

Theorem day_never_repeats : forall d : day, next_day d <> d.

(** Again, you might say "that's obvious."  But in this case, it's not obvious
enough for [auto] to find a proof. *)

Proof. auto.

(** So here's a better strategy:  consider all the possible values that [d]
could have: [sun], [mon], etc.  Now consider instantiating what the theorem says
for each:

- [next_day sun <> sun]
- [next_day mon <> mon]
- etc.

In each case, if we reduce the expression on the left to a value, we get an
inequality that's more obviously true:

- [mon <> sun]
- [tue <> mon]
- etc.

The reason that [mon <> sun] is that they are different constructors of an
inductive (i.e., variant) type, and different constructors can never be equal.

This is a proof strategy that Coq will understand.  To implement it, we need two
new tactics:

- [destruct] is a tactic that considers all the possible ways to construct
  an inductive type.

- [discriminate] is a tactic that proves different constructors cannot be equal.
*)


  intros d. destruct d.
  simpl. discriminate.
  simpl. discriminate.
  simpl. discriminate.
  simpl. discriminate.
  simpl. discriminate.
  simpl. discriminate.
  simpl. discriminate.

Qed.

(** The first step of this proof, [intros d], _introduces_ [d].  Think of it
like saying "let [d] be some arbitrary [day]."  The second step of the proof,
[destruct d], instructs Coq to do case analysis on [d].  The next seven lines
apply [simpl] then [discriminate] 7 times, once for each possible day in the
case analysis.

That repetition of the same tactic is rather ugly.  First, we don't actually
need to use [simpl].  In fact, [discriminate] will do simplification itself, as
will many other tactics.  Second, instead of writing [discriminate] 7 times, we
could instead write [all: discriminate].  That means to use [discriminate] on
all the remaining _subgoals_ in the proof. *)

Theorem day_never_repeats' : forall d : day, next_day d <> d.
Proof.
  intros d. destruct d.
  all: discriminate.
Qed.

(** Another way to structure that proof is with the semicolon _tactical_, which
chains together tactics.  The tactic [t1; t2] means to apply tactic [t1], then
further apply tactic [t2] to all the subgoals generated by [t1]. *)

Theorem day_never_repeats'' : forall d : day, next_day d <> d.
Proof.
  intros d. destruct d; discriminate.
Qed.

(** Now let's prove that if the day after [d] is [tue], then [d] must be [mon].
To express that implication in a theorem we use the symbol [->], where [A -> B]
means that if [A] is true, then so is [B]. *)
Theorem mon_preceds_tues : forall d : day,
  next_day d = tue -> d = mon.

(** Why does that theorem hold?  An informal argument by case analysis would say
that of all the 7 possible values of [d], 6 of them immediately fail to make
[next_day d = true] hold,  In fact, only [d=mon] does.  So for each of the 7
cases, we either have a contradiction, _or_ we have a trivial equality.  In Coq,
we can express that proof as follows, where we use a new tactical [||] for "or".
*)

Proof.
  intros.
  destruct d.
  all: discriminate || trivial.
Qed.

(**
Let's pick apart that proof.

- The first line introduces two assumptions into the proof:  that [d] is a [day],
  and that [next_day d = tue].  The latter is the _antecedent_ of the
  implication that is being proved, i.e., the [P] in [P -> Q]; [Q] is called the
  _consequent_. We chose the name [next_day_is_tue] to record that assumption.
  Idiomatically, Coq programmers will often use short names like [H] for these
  kinds of _hypotheses_.

- The second line does the case analysis on [d] as we did before.

- The third line says to use [discriminate || trivial] on all the subgoals.
  That works like a short-circuit OR in OCaml:  if [discriminate] fails
  to find a proof of the subgoal, then [trivial] will be used to find
  the proof instead.
*)

(**********************************************************************)


(**
** Lists

The Coq standard library includes lists.  Some parts of the list library are
already included by default, but not all are.  To load the full list library, we
need to issue the following commands: *)

Require Import List.
Import ListNotations.

(** Coq lists are defined in essentially the same way as OCaml lists.  A list is
may contain any number of elements, and each element must have the same type.
The empty list is represented with [nil], and [cons] creates a new list out of
an element and an already existing list. The standard library defines lists as
follows: *)

Module MyList.

Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

End MyList.

(** (We wrapped that definition in its own [Module] so that, in the rest
of this file, [list] still means the [list] in the standard library
as opposed to the one we just defined ourselves.) *)

(**
Let's compare that to a similar OCaml definition of lists:
<<
type 'a list = 
| Nil 
| Cons of 'a * 'a list
>>
The ['a] is a type variable in the OCaml definition.  Similarly, in the
Coq definition, [list (A : Type) : Type] indicates that [list] is
parameterized on a type [A].  Hence Coq's [list] is a type constructor
just like OCaml's [list] is.  In fact, if we check the type of [list],
this becomes even clearer:
*)

Check list.

(**
<<
list : Type -> Type
>>

That is, [list] takes a type as input and returns a type as output.

Also, notice the branches:
<<
| nil : list A
| cons : A -> list A -> list A.
>>

These say that [nil] already has type [list A], for any [A], and that [cons] is
a _function_ that takes an [A] and a [list A] and returns a [list A].  So Coq's
[cons] is truly a function, unlike OCaml's.  (In OCaml you can't, for example,
pass a constructor name to a function.)

We can use pattern matching to code functions that take lists as inputs,
just like in OCaml.
*)

Definition is_empty (A : Type) (lst : list A) :=
  match lst with
  | nil => true
  | cons _ _ => false
  end.

(** In [is_empty], we have explicitly given type annotations on two arguments.
The first argument, [A], is the type of the list elements.  The second argument,
[lst], has type [list A]. OCaml never made us explicitly write down the element
type as an input to functions, because the language is engineered to guarantee
that type inference can always figure out those types.  Coq's type system,
however, is _vastly_ more expressive that OCaml's, hence type inference is a
hard problem in Coq.  Coq is therefore more strict about writing these things
down.

Like in OCaml, we can use syntactic sugar for lists, writing [[]] for [nil]
and [::] for [cons]: *)

Definition is_empty_sugar (A : Type) (lst : list A) :=
  match lst with
  | [] => true
  | _::_ => false
  end.

(** If we want to compute with [is_empty], we have to supply the type argument:
*)

Compute is_empty nat [1].

Compute is_empty nat [].

(**
In the second computation above, it wouldn't matter what type we pass in because
the list is empty, but we do have to provide _some_ type as an argument.
There are various ways in Coq of making this type argument something that
the compiler infers, instead of the programmer having to provide.  These
are called _implicit arguments_.  Here's one way to make an argument
implicit:
*)

Definition is_empty' {A : Type} (lst : list A) :=
  match lst with
  | [] => true
  | _::_ => false
  end.

Compute is_empty' [1].

(**
We put the [A:Type] parameter in braces instead of parentheses.  This tells
Coq that the argument should be inferred.  As you can see, we didn't
provide it in the example usage.   In fact, Coq would reject
[is_empty' nat [1]], because once we've made the argument implicit,
we're actually not even allowed to provide it.

If for some reason we really did need to explicitly provide an
implicit argument, we could do that by prefixing the name of the
function with [@].  For example:
*)

Compute @is_empty' nat [1].

(** To define recursive functions on lists, instead of OCaml's [let rec], Coq
uses [Fixpoint] as a keyword. That perhaps-cryptic name comes from programming
languages theory, where recursion can be defined as a so-called _fixed point_ of
a function.

Here is a definition of [length] for lists, and an example usage.  Again,
we do this in its own module to avoid clashing with the standard library's
definition of [length].
*)

Module MyLength.

Fixpoint length {A : Type} (lst : list A) :=
  match lst with
  | nil => 0
  | _::t => 1 + length t
  end.

Compute length [1;2].

End MyLength.

(**********************************************************************)

(**
** Options

In the Coq standard library, options are defined as follows.
(Once more we wrap the definition in its own module to avoid
clashing with the standard library's own definition.)
*)

Module MyOption.

Inductive option (A:Type) : Type :=
  | Some : A -> option A
  | None : option A.

End MyOption.

(** Coq options are essentially the same as OCaml's.  [Some] is a function that
given a value of type [A], constructs an option containing that value.  [None]
is already a value that has type [option A] for any [A].

Here is a function [hd_opt].  It returns the head of a list, wrapped in [Some].
If the list is empty, it returns [None]. *)

Definition hd_opt {A : Type} (lst : list A) : option A :=
  match lst  with
  | nil => None
  | x :: _ => Some x
  end.

Compute hd_opt [1].

Compute @hd_opt nat [].

(** The first of those example usages returns [Some 1 : option nat], and the
second returns [None : option nat].  In the second, we are forced to explicitly
provide the type argument, because Coq can't infer from just the empty list what
kind of option it should be:  should it be [option nat]? [option bool]? or
something else? *)

(** Now let's prove something about [hd_opt]:  when applied to a list of length
0, it returns [None]. Informally, that holds because there are two possibilities
of how a list is constructed:

- if the list is [nil], then its length is certainly 0, and evaluation of
  [hd_opt]'s pattern match will choose the branch that returns [None].

- if the list is constructed with [cons], then its length is at least 1.  That
  contradicts the assumption that its length is 0.

The proof below uses exactly that reasoning.
*)

Theorem length0_implies_hdopt_is_none :
  forall (A : Type) (lst : list A),
    length lst = 0 -> hd_opt lst = None.
Proof.
  intros A lst length_lst_is_0.
  destruct lst.
    trivial.
    discriminate.
Qed.

(** The first line of that proof, which uses the [intros] tactic, introduces
three assumptions into the proof:  That [A] is a type, that [lst] has type [list
A], and that the length of [lst] is 0.  The second line does the case analysis
on [lst]:  is it [nil] or [cons]?  The next two tactics handle each of those
cases.

- The first case, where the list is [nil], is handled by [trivial], which finds
  a proof that [hd_opt nil = None].  It succeeds in doing that by first doing
  some computation, which reduces [hd_opt nil] to [None], then showing that
  [None = None] because equality is reflexive.

- The second case, where the list is [cons], is handled by [discriminate],
  which finds a contradiction while trying to prove that [hd_opt (a :: lst) =
  None]. Of course, that equality is untrue:  [hd_opt (a :: lst)] is actually
  [Some a]. So [discriminate] looks in the hypotheses of the proof and finds one
  that claims [length (a :: lst) = 0].  Of course, that's untrue, because
  [length (a :: lst)] is [1 + length lst], which is at least 1, and [1 <> 0].
  The [discriminate] tactic detects that contradiction.  You might recall from
  CS 2800 that from an assumption of [false], you are allowed to conclude
  anything. That's the reasoning being used here.

When there are a few cases in a proof, as there were (two) in the previous
proof, sometimes Coq programmers use _bullets_ to make the structure of their
proofs apparent to readers.  The bullets also help with _focusing_ the
programmer's attention on the proof state during the process of constructing the
proof. The bullets in the proof below, written [-], cause all but one subgoal to
disappear.  After a subgoal has been proved, the proof state reads "There are
unfocused goals."  The next bullet causes the next unfocused goal to become
focused.  This is probably best understood by stepping through the following
proof in Coq and observing what happens to the proof state when each bullet is
processed. *)

Theorem length0_implies_hdopt_is_none' :
forall (A : Type) (lst : list A),
  length lst = 0 -> hd_opt lst = None.
Proof.
  intros A lst length_lst_is_0.
  destruct lst.
    - trivial.
    - discriminate.
Qed.

(** The characters [+] and [*] can also be used as bullets, as can [--], [---],
etc.

(**********************************************************************)


** Summary

Coq is a functional programming language.  It contains many of the same features
as OCaml.  In fact, Coq is implemented in OCaml.  Coq is also a proof assistant.
We can write programs and prove theorems about those programs.  Coq searches for
those proofs, and we guide its search with tactics.

** Terms and concepts

- antecedent
- case analysis
- consequent
- constructor
- definition
- fixpoint
- function
- goal
- hypothesis
- implicit argument
- inductive type
- proof search
- proof state
- reflexivity of equality
- tactic
- tactical
- theorem

** Tactics

- [auto]
- [destruct]
- [discriminate]
- [intros]
- [simpl]
- [trivial]
- tacticals: [all], [||], [;], [-], [*], [+]

** Further reading

- _Software Foundations, Volume 1: Logical Foundations_.
  #<a href="https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html">
  Chapter 1: Basics.</a>#

- _Interactive Theorem Proving and Program Development_.
  Chapters 1 through 4. Available
  #<a href="https://newcatalog.library.cornell.edu/catalog/10131206">
  online from the Cornell library</a>#.
*)
