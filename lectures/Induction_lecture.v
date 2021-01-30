(**
* Induction in Coq

  From: https://www.cs.cornell.edu/courses/cs3110/2018sp/l/22-coq-induction/notes.v
-----
#<i>#
Topics:

- recursive functions
- induction on lists
- induction on natural numbers
- rings and fields
- induction principles
- extraction

#</i>#

-----

We'll need the list library for these notes.
*)

Require Import List.
Import ListNotations.

(**

(**********************************************************************)

** Recursive functions

The [List] library defines the list append operator, which in Coq is written as
infix operator [++], or as prefix function [app].  In OCaml, the same operator
is written [@].  In OCaml's standard library, you'll recall that append
is defined as follows:

<<
let rec append lst1 lst2 =
  match lst1 with
  | [] -> lst2
  | h::t -> h :: (append t lst2)
>>

The Coq equivalent of that would be: *)

Fixpoint append {A : Type} (lst1 : list A) (lst2 : list A) :=
  match lst1 with
  | nil => lst2
  | h::t => h :: (append t lst2)
  end.

(** The [Fixpoint] keyword is similar to a [let rec] definition in OCaml. The
braces around [A : Type] in that definition make the [A] argument implicit,
hence we don't have to provide it at the recursive call to [append] in the
second branch of the pattern match.  Without the braces, we'd have to write the
function as follows: *)

Fixpoint append' (A : Type) (lst1 : list A) (lst2 : list A) :=
match lst1 with
| nil => lst2
| h::t => h :: (append' A t lst2)
end.

(** The actual definition of [++] in the Coq standard library is a little more
complicated, but it's essentially the same idea.  Here's that definition:

<<
Definition app (A : Type) : list A -> list A -> list A :=
  fix app' lst1 lst2 :=
    match lst1 with
    | nil => lst2
    | h :: t => h :: app' t lst2
    end.
>>

The Coq [fix] keyword is similar to a [let rec] expression in OCaml, but where
the body of the expression is implicit:  Coq [fix f x1 .. xn := e] is like OCaml
[let rec f x1 .. xn = e in f].  So in OCaml we could rephrase the above
definition as follows:

<<
let app : 'a list -> 'a list -> 'a list =
  let rec app' lst1 lst2 =
    match lst1 with
    | [] -> lst2
    | h :: t -> h :: app' t lst2
  in
  app'
>>

Now that we know how Coq defines [++], let's prove a theorem about it.
*)

Theorem nil_app : forall (A:Type) (lst : list A),
  [] ++ lst = lst.

(** Intuition:  appending the empty list to [lst] immediately returns
    [lst], by the definition of [++]. *)

Proof.
  intros A lst.
  simpl.
  trivial.
Qed.

(** The second step in that proof simplifies [[] ++ lst] to [lst].  That's
because of how [++] is defined:  it pattern matches against its first argument,
which here is [[]], hence simply returns its second argument.

Next, let's prove that appending nil on the right-hand side also results in
[lst]: *)

Theorem app_nil : forall (A:Type) (lst : list A),
  lst ++ [] = lst.

(* Intuition (incomplete):  by case analysis on [lst].
   - if [lst] is [[]], then trivially [[] ++ []] is [[]].
   - if [lst] is [h::t], then ...? *)

Proof.
  intros A lst. destruct lst as [ | h t].
  - trivial.
  - simpl.  (* can't proceed *)
Abort.

(** When we get to the end of that proof, we are trying to show that [h :: (t ++
[]) = h :: t].  There's no way to make progress on that, because we can't
simplify [t ++ []] to just [t].  Of course as humans we know that holds.  But to
Coq, that's a fact that hasn't yet been proved.  Indeed, it is an instance of
the theorem we're currently trying to prove!

What's going wrong here is that case analysis is not a sufficiently powerful
proof technique for this theorem.  We need to be able to _recursively_ apply the
theorem we're trying to prove to smaller lists.  That's where _induction_ comes
into play.

(**********************************************************************)

** Induction on lists

_Induction_ is a proof technique that you will have encountered in math
classes before---including CS 2800.  It is useful when you want to prove
that some property holds of all the members of an infinite set, such as
the natural numbers, as well as lists, trees, and other data types.

One classic metaphor for induction is _falling dominos_:  if you arrange some
dominos such that each domino, when it falls, will knock over the next domino,
and if you knock over the first domino, then all the dominos will fall. Another
classic metaphor for induction is a _ladder_:  if you can reach the first rung,
and if for any given rung the next rung can be reached, then you can reach any
rung you wish.  (As long as you're not afraid of heights.)

What both of those metaphors have in common is

- a _base case_, in which something is done first.  For the dominos, it's
  knocking over the first domino; for the ladder, it's climbing the first rung.
  And,

- an _inductive case_, in which a step is taken from one thing to the
  the next.  For the dominos, it's one domino knocking over the next; for the
  ladder, it's literally taking the step from one rung to the next.  In both
  cases, it must actually be possible for the action to occur:  if the dominos
  or the rungs were spaced too far apart, then progress would stop.

A proof by induction likewise has a base case and an inductive case.
Here's the structure of a proof by induction on a list:

<<
Theorem.  For all lists lst, P(lst).

Proof.  By induction on lst.

Case:  lst = nil
Show:  P(nil)

Case:  lst = h::t
IH:    P(t)
Show:  P(h::t)

QED.
>>

The _base case_ of a proof by induction on lists is for when the list is empty.
The _inductive case_ is when the list is non-empty, hence is the cons of a head
to a tail.  In the inductive case, we get to assume an _inductive hypothesis_,
which is that the property [P] holds of the tail.

In the metaphors above, the inductive hypothesis is the assumption that we've
already reached some particular domino or rung.  From there, the metaphorical
work we do in the inductive case of the proof is to show that from that domino
or rung, we can reach the next one.

An inductive hypothesis is exactly the kind of assumption we needed to get our
proof about appending nil to go through.

Here's how that proof could be written:

<<
Theorem:  for all lists lst, lst ++ nil = lst.

Proof:  by induction on lst.
P(lst) = lst ++ nil = lst.

Case:  lst = nil
Show:
  P(nil)
= nil ++ nil = nil
= nil = nil

Case:  lst = h::t
IH: P(t) = (t ++ nil = t)
Show
  P(h::t)
= (h::t) ++ nil = h::t
= h::(t ++ nil) = h::t     // by definition of ++
= h::t = h::t              // by IH

QED
>>

In Coq, we could prove that theorem as follows:
*)

Theorem app_nil : forall (A:Type) (lst : list A),
  lst ++ nil = lst.
Proof.
intros A lst. induction lst as [ | h t IH].
- simpl. trivial.
- simpl. rewrite -> IH. trivial.
Qed.



(** The tactics used in that proof correspond exactly to the non-Coq proof
above.

The [induction] tactic is new to us.  It initiates a proof by induction on its
argument, in this case [lst], and provides names for the variables to be used in
the cases.  There aren't any new variables in the base case, but the inductive
case has variables for the head of the list, the tail, and the inductive
hypothesis.  You could leave out those variables and simply write [induction
lst.], but that leads to a less human-readable proof.

In the inductive case, we use the [rewrite ->] tactic to rewrite [t ++
nil] to [t].  The [IH] says those terms are equal.  That tactic replaces the
left-hand side of the equality with the right-hand side, wherever the left-hand
side appears in the subgoal. It's also possible to rewrite from right to left
with the [rewrite <-] tactic.  If you leave out the arrow, Coq assumes that
you mean [->].

Here's another theorem we can prove in exactly the same manner. This
theorem shows that append is _associative_.

<<
Theorem:  forall lists l1 l2 l3, l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.

Proof: by induction on l1.
P(l1) = l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3

Case:  l1 = nil
Show:
  P(nil)
= nil ++ (l2 ++ l3) = (nil ++ l2) ++ l3
= l2 ++ l3 = l2 ++ l3   // simplifying ++, twice

Case:  l1 = h::t
IH:  P(t) = t ++ (l2 ++ l3) = (t ++ l2) ++ l3
Show:
  P(h::t)
= h::t ++ (l2 ++ l3) = (h::t ++ l2) ++ l3
= h::(t ++ (l2 ++ l3)) = h::((t ++ l2) ++ l3)  // simplifying ++, thrice
= h::((t ++ l2) ++ l3) = h::((t ++ l2) ++ l3)  // by IH

QED
>>

In Coq, that proof looks more or less identical to our previous Coq proof
about append and nil:
*)

Theorem app_assoc : forall (A:Type) (l1 l2 l3 : list A),
  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
(* Intuition: above *)
Proof.
  intros A l1 l2 l3.
  induction l1 as [ | h t IH].
  - simpl. trivial.
  - simpl. rewrite -> IH. trivial.
Qed.

(**
(**********************************************************************)

** Induction on natural numbers

One of the classic theorems proved by induction is that [0 + 1 + ... + n] is
equal to [n * (n+1) / 2].  It uses proof by induction on the natural numbers,
which are the non-negative integers.  The structure of a proof by induction on
the naturals is as follows:

<<
Theorem.  For all natural numbers n, P(n).

Proof.  By induction on n.

Case:  n = 0
Show:  P(0)

Case:  n = k+1
IH:    P(k)
Show:  P(k+1)

QED.
>>

The base case is for zero, the smallest natural number.  The inductive case
assumes that P holds of k, then shows that P holds of k+1.

The [induction] tactic in Coq works for inductive types---that is, types defined
with the [Inductive] keyword.  You might, therefore, suspect that if we're going
to do induction over [nat]s, the type [nat] must be inductively defined.  Indeed
it is.  There is a famous inductive definition of the natural numbers that is
credited to Giuseppe Peano (1858-1932).  In OCaml, that definition would be:

<<
type nat = O | S of nat
>>

The [O] constructor (that's the letter capital O) represents zero.
The [S] constructor represents the successor function---that is, the
function that adds one to its argument.  So:

- 0 is [O]
- 1 is [S O]
- 2 is [S (S O)]
- 3 is [S (S (S O))]
- etc.

This is a kind of _unary_ representation of the naturals, in which we repeat
the symbol [S] a total of [n] times to represent the natural number [n].

The Coq definition of [nat] is much the same:
*)

Print nat.

(**
Coq responds with output that is equivalent to the following:
<<
Inductive nat : Set :=
  | O : nat
  | S : nat -> nat
>>

That is, [nat] has two constructors, [O] and [S], which are just like the OCaml
constructors we examined above.  And [nat] has type [Set], meaning that [nat] is
a specification for program computations.  (Or, a little more loosely, that
[nat] is a type representing program values.)

Anywhere we write something that looks like an integer literal in Coq, Coq
actually understand that as its expansion in the Peano representation defined
above.  For example, [2] is understood by Coq as just syntactic sugar for [S (S
O)].  We can even write computations using those constructors:
*)

Compute S (S O).

(**
Coq responds, though, by reintroducing the syntactic sugar:
<<
= 2 : nat
>>

The Coq standard library defines many functions over [nat] using those
constructors and pattern matching, including addition, subtraction,
and multiplication.  For example, addition is defined like this:
*)

Fixpoint my_add (a b : nat) : nat :=
  match a with
  | 0 => b
  | S c => S (my_add c b)
  end.

(**
Note that we're allowed to use either [0] or [O] as a pattern, because
the former is just syntactic sugar for the latter.  The second branch
of the pattern match is effectively calling [my_add] recursively with
[a-1] as its first argument, since [a = S c], meaning that [a] is the
successor of [c].

Now that we know how [nat] is defined inductively, let's try
to prove the classic theorem mentioned above about summation.
Moreover, let's prove that a program that computes the sum [0 + 1 + ... + n]
does in fact compute [n * (n+1) / 2].  First, we need to write
that program.  In OCaml, we could write the program quite easily:
<<
let rec sum_to n =
  if n=0 then 0
  else n + sum_to (n-1)
>>

In Coq, it will turn out to be surprisingly tricky...

(**********************************************************************)

** Recursive functions, revisited

Here's a first attempt at defining [sum_to], which is just a direct translation
of the OCaml code into Coq.  The [Fail] keyword before it tells Coq to expect
the definition to fail to compile. *)

Fail Fixpoint sum_to (n:nat) : nat :=
  if n = 0 then 0 else n + sum_to (n-1).

(**
Coq responds:
<<
The command has indeed failed with message:
The term "n = 0" has type "Prop"
which is not a (co-)inductive type.
>>
The problem is the the equality operator [=] returns a proposition (i.e.,
something we could try to prove), whereas the [if] expression expects a Boolean
(i.e., [true] or [false]) as its guard. (Actually [if] is willing to accept any
value of an inductive type with exactly two constructors as its guard, and
[bool] is an example of such a type.)

To fix this problem, we need to use an equality operator that returns a [bool],
rather than a [Prop], when applied to two [nat]s.  Such an operator is defined
in the [Arith] library for us: *)

Require Import Arith.

Locate "=?".
Check Nat.eqb.

(** Coq responds:
<<
Nat.eqb : nat -> nat -> bool
>>

We can now try to use that operator.  Unfortunately, we discover a new problem:
*)

Fail Fixpoint sum_to (n:nat) : nat :=
  if n =? 0 then 0 else n + sum_to (n-1).

(** Coq responds with output that contains the following lines:
<<
Recursive definition of sum_to is ill-formed.
...
Recursive call to sum_to has principal argument equal to
"n - 1" instead of a subterm of "n".
...
>>
Although the error message might be cryptic, you can see that Coq is complaining
about the recursive call in the [else] branch.  For some reason, Coq is unhappy
about the argument [n-1] provided at that call.  Coq wants that argument to be a
"subterm" of [n].  The words _term_ and _expression_ are synonymous here, so Coq
is saying that it wants the argument to be a subexpression of [n].  Of course
[n] doesn't have any subexpressions. So why is Coq giving us this error?

Before we can answer that question, let's look at a different recursive
function---one that implements an infinite loop: *)

Fail Fixpoint inf (x:nat) : nat := inf x.

(**
Coq responds very similarly to how it did with [sum_to]:
<<
Recursive definition of inf is ill-formed.
...
Recursive call to inf has principal argument equal to
"x" instead of a subterm of "x".
>>

The reason Coq rejects [inf] is that #<b>Coq does not permit any infinite
loops</b>#. That might seem strange, but there's an excellent reason for it.
Consider how [inf] would be defined in OCaml:
<<
# let rec inf x = inf x
val inf : 'a -> 'b = <fun>
>>
Let's look at the type of that function, using what we learned about
propositions-as-types in the previous lecture.  The type ['a -> 'b]
corresponds to the proposition [A -> B], where [A] and [B] could
be any propositions.  In particular, [A] could be [True] and [B]
could be [False], leading to the proposition [True -> False].  That's
a proposition that should never be provable:  truth does not imply
falsehood.  And yet, since [inf] is a program of that type, [inf]
corresponds to a proof of that proposition.  So using [inf] we could
actually prove [False]:
<<
type void = {nope : 'a . 'a};;
let rec inf x = inf x;;
let ff : void = inf ();;
>>
The [void] type is how we represented [False] in the previous lecture.
The value [ff] above corresponds to a proof of [False].
So infinite loops are able to prove [False].

In OCaml we don't mind that phenomenon, because OCaml's purpose is not to be a
proof assistant.  But in Coq it would be deadly:  we should never allow the
proof assistant to prove false propositions.  Coq therefore wants to prohibit
all infinite loops.  But that's easier said than done!  Recall from CS 2800 that
the _halting problem_ is undecidable:  we can't write a program that precisely
determines whether another program will terminate.  Well, the Coq compiler is a
program, and it wants to detect which programs terminate and which programs do
not---which is exactly what the halting problem says is impossible.

So instead of trying to do something impossible, Coq settles for doing something
possible but imprecise, specifically, something that prohibits all
non-terminating programs as well as prohibiting some terminating programs. Coq
enforces a syntactic restriction on recursive functions: there must always be an
argument that is _syntactically smaller_ at every recursive function
application.  An expression [e1] is syntactically smaller than [e2] if [e1] is a
subexpression of [e2].  For example, [1] is syntactically smaller than [1-x],
but [n-1] is not syntactically smaller than [n].  It turns out this restriction
is sufficient to guarantee that programs must terminate:  eventually, if every
call results in something smaller, you must reach something that is small enough
that you cannot make a recursive call on it, hence evaluation must terminate.  A
synonym for "syntactically smaller" is _structurally decreasing_.

But that does rule out some programs that we as humans know will terminate yet
do not meet the syntactic restriction.  And [sum_to] is one of them. Here is the
definition we previously tried: *)

Fail Fixpoint sum_to (n:nat) : nat :=
  if n =? 0 then 0 else n + sum_to (n-1).

(** The recursive call to [sum_to] has as its argument [n-1], which
syntactically is actually bigger than the original argument of [n].  So Coq
rejects the program.

To finally succeed in definining [sum_to], we can make use of what we know about
how [nat] is defined:  since it's an inductive type, we can pattern match on it:
*)

Fixpoint sum_to (n:nat) : nat :=
  match n with
  | 0 => 0
  | S k => n + sum_to k
  end.

(** The second branch of the pattern match recurses on an argument that is both
syntactically and arithmetically smaller, just as our definition of [my_add]
did, above.  So Coq's syntactic restriction on recursion is satisfied, and the
definition is accepted as a program that definitely terminates.


<<--------CS6225 STOPPED HERE-------->>


(**********************************************************************)

** Inductive proof of the summation formula

Now that we've finally succeeded in defining [sum_to], we can prove
the classic theorem about summation.

Here's how we would write the proof mathematically:

<<
Theorem:  for all natural numbers n, sum_to n = n * (n+1) / 2.

Proof:  by induction on n.
P(n) = sum_to n = n * (n+1) / 2

Case:  n=0
Show:
  P(0)
= sum_to 0 = 0 * (0+1) / 2
= 0 = 0 * (0+1) / 2         // simplifying sum_to 0
= 0 = 0                     // 0 * x = 0

Case:  n=k+1
IH:  P(k) = sum_to k = k * (k+1) / 2
Show:
  P(k+1)
= sum_to (k+1) = (k+1) * (k+1+1) / 2
= k + 1 + sum_to k = (k+1) * (k+1+1) / 2          // simplifying sum_to (k+1)
= k + 1 + k * (k+1) / 2 = (k+1) * (k+1+1) / 2     // using IH
= 2 + 3k + k*k = 2 + 3k + k*k                     // simplifying terms on each side

QED
>>

Now let's do the proof in Coq. *)

Theorem sum_sq : forall n : nat,
  sum_to n = n * (n+1) / 2.
Proof.
  intros n.
  induction n as [ | k IH].
  - trivial.
  - simpl. rewrite -> IH.
Abort.


(** The proof is working fine so far, but now we have a complicated algebraic
equation we need to prove:
<<
S (k + k * (k + 1) / 2) = fst (Nat.divmod (k + 1 + k * S (k + 1)) 1 0 0)
>>
([divmod] is part of how [/] is implemented in Coq.)

Although we could try to prove that manually using the definitions of all the
operators, it would be much nicer to get Coq to find the proof for us.  It turns
out that Coq does have great support for finding proofs that involve _rings_:
algebraic structures that support addition and multiplication operations.
(We'll discuss rings in detail after we finish the current proof.)  But we can't
use that automation here, because the equation we want to prove also involves
division, and rings do not support division operations.

To avoid having to reason about division, we could rewrite the theorem we want
to prove:  by multiplying both sides by 2, the division goes away: *)

Theorem sum_sq_no_div : forall n : nat,
  2 * sum_to n = n * (n+1).
Proof.
  intros n.
  induction n as [ | k IH].
  - trivial.
  - simpl.
Abort.

(** Now, after the call to [simpl], we don't have any division, but we also
don't have any expressions that look exactly like the left-hand side of the
inductive hypothesis.  The problem is that [simpl] was too agressive in
simplifying all the expressions. All we really want is to transform the
left-hand side of the subgoal, [2 * sum_to (S k)], into an expression that
contains the left-hand side of the inductive hypothesis, [2 * sum_to k].
Thinking about the definition of [sum_to], we ought to be able to transform 

[2 * sum_to (S k)] 

into 

[2 * (S k + sum_to k)]

, which equals 

[2 * (S k) + 2 * sum_to k].  

That final expression does have the left-hand side of the inductive
hypothesis in it, as desired.  Let's factor out that reasoning as a separate
"helper" theorem.  In math, helper theorems are usually called _lemmas_.  The
Coq keyword [Lemma] is synonymous with [Theorem]. *)

Lemma sum_helper : forall n : nat,
  2 * sum_to (S n) = 2 * (S n) + 2 * sum_to n.
Proof.
  intros n. simpl. ring.
Qed.

(** The proof above simplifies the application of [sum_to (S n)], then invokes a
new tactic called [ring].  That tactic is able to automatically search for
proofs of equations involving addition and multiplication of natural numbers.

Now that we have our helper lemma, we can use it to prove the theorem: *)

Theorem sum_sq_no_div : forall n : nat,
  2 * sum_to n = n * (n+1).
Proof.
  intros n.
  induction n as [ | k IH].
  - trivial.
  - rewrite -> sum_helper.
    rewrite -> IH.
    ring.
Qed.

(** Once more, after doing the rewriting with the lemma and the inductive
hypothesis, we're left with algebraic equations that can be proved simply by
invoking the [ring] tactic.

Finally, we can use [sum_sq_no_div] to prove the original theorem involving
division.  To do that, we need to first prove another lemma that shows we can
transform a multiplication into a division: *)

Lemma div_helper : forall a b c : nat,
  c <> 0 -> c * a = b -> a = b / c.
Proof.
  intros a b c neq eq.
  rewrite <- eq.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul.
  trivial.
  assumption.
Qed.

Check Nat.mul_comm.

(**
That lemma involves two library theorems, [mult_comm] and [Nat.div_mul]. How
did we know to use these?  Coq can help us search for useful theorems. Right
after we [rewrite <- eq] in the above proof, our subgoal is [a = c * a / c]. It
looks like we ought to be able to cancel the [c] term on the right-hand side.
So we can search for a theorem that would help us do that.  The [Search] command
takes wildcards and reports all theorems that match the pattern we supply, for
example:
*)

Search (_ * _ / _).

(** This reveals a useful theorem:
<<
Nat.div_mul: forall a b : nat, b <> 0 -> a * b / b = a
>>
That would let us cancel a term from the numerator and denominator, but it
requires the left-hand side of the equality to be of the form [a * b / b],
whereas we have [c * a / c].  The problem is that the two sides of the
multiplication are reversed.  No worries; multiplication is commutative, and
there is a library theorem that proves it. Again, we could find that theorem: *)

Search (_ * _ = _ * _).

(** One of the results is:
<<
Nat.mul_comm: forall n m : nat, n * m = m * n
>>

Putting those two library theorems to use, we're able to prove the lemma as
above.

Finally, we can use that lemma to prove our classic theorem about summation. *)

Theorem sum_sq : forall n : nat,
  sum_to n = n * (n+1) / 2.
Proof.
  intros n.
  apply div_helper.
  - discriminate.
  - rewrite sum_sq_no_div. trivial.
Qed.

(** When we use [apply div_helper] in that proof, Coq generates two new
subgoals---one for each of the propositions [c <> 0] and [c * a = b] in the type
of [div_helper].

_Summary_:  wow, that was a lot of work to prove that seemingly simple classic
theorem!  We had to figure out how to code [sum_to], and we had to deal with a
lot of complications involving algebra.  This situation is not uncommon:  the
theorems that we think of as easy with pencil-and-paper (like arithmetic) turn
out to be hard to convince Coq of, whereas the theorems that we think of as
challenging with pencil-and-paper (like induction) turn out to be easy.

(**********************************************************************)

** Rings and fields

In the proof we just did above about summation, we used a tactic called [ring]
that we said searches for proofs about algebraic equations involving
multiplication and addition.  Let's look more closely at that tactic.

When we studied OCaml modules, we looked at _rings_ as an example of a
mathematical abstraction of addition, multiplication, and negation.  Here is an
OCaml signature for a ring:

<<
module type Ring = sig
  type t
  val zero : t
  val one  : t
  val add  : t -> t -> t
  val mult : t -> t -> t
  val neg  : t -> t
end
>>

We could implement that signature with a representation type [t] that is [int],
or [float], or even [bool].

The names given in [Ring] are suggestive of the operations they represent, but
to really specify how those operations should behave, we need to write some
equations that relate them.  Below are the equations that (it turns out) fully
specify [zero], [one], [add], and [mult].  Rather than use those identifiers, we
use the more familiar notation of [0], [1], [+], and [*].

<<
0 + x = x
x + y = y + x
x + (y + z) = (x + y) + z

0 * x = 0
1 * x = 1
x * y = y * x
x * (y * z) = (x * y) * z

(x + y) * z = (x * z) + (y * z)
>>

Technically these equations specify what is known as a _commutative semi-ring_.
It's a _semi_-ring because we don't have equations specifying negation yet.
It's a _commutative_ semi-ring because the [*] operation commutes. (The [+]
operation commutes too, but that's always required of a semi-ring.)

The first group of equations specifies how [+] behaves on its own. The second
group specifies how [*] behaves on its own. The final equation specifies how [+]
and [*] interact.

If we extend the equations above with the following two, we get a specification
for a _ring_:

<<
x - y = x + (-y)
x + (-x) = 0
>>

It's a remarkable fact from the study of _abstract algebra_ that those equations
completely specify a ring.  Any theorem you want to prove about addition,
multiplication, and negation follows from those equations.  We call the
equations the _axioms_ that specify a ring.

Rings don't have a division operation.  Let's introduce a new operator called
[inv] (short for "inverse"), and let's write [1/x] as syntactic sugar for [inv
x].  If we take all the the ring axioms and add the following axiom for [inv],
we get what is called a _field_:

<<
x * 1/x = 1     if x<>0
>>

A field is an abstraction of addition, multiplication, negation, and division.
Note that OCaml [int]s do not satisfy the [inv] axiom above.  For example, [2 *
(1/2)] equals [0] in OCaml, not [1].  OCaml [float]s mostly do satisfy the field
axioms, up to the limits of floating-point arithmetic.  And in mathematics, the
rational numbers and the real numbers are fields.

Coq provides two tactics, [ring] and [field], that automatically search for
proofs using the ring and field axioms. The [ring] tactic was already loaded for
us when we wrote [Require Import Arith] earlier in this file. We can use the
[ring] tactic to easily prove equalities that follow from the ring axioms.  Here
are two examples. *)

Theorem plus_comm : forall a b,
  a + b = b + a.
Proof.
  intros a b. ring.
Qed.

Theorem foil : forall a b c d,
  (a + b) * (c + d) = a*c + b*c + a*d + b*d.
Proof.
  intros a b c d. ring.
Qed.

(** Coq infers the types of the variables above to be [nat], because the [+] and
[*] operators are defined on [nat].

The proofs that the [ring] tactic finds can be quite complicated.  For example,
try looking at the output of the following command.  It's so long that we won't
put that output in this file! *)

Print foil.

(** Of course, [ring] won't find proofs of equations that don't actually hold.
For example, if we had a typo in our statement of [foil], then [ring] would
fail. *)

Theorem broken_foil:  forall a b c d,
  (a + b) * (c + d) = a*c + b*c + c*d + b*d.
Proof.
  intros a b c d. try ring.
Abort.

(** Here's a theorem that [ring], perhaps surprisingly, cannot prove. *)

Theorem sub_add_1 : forall a : nat, a - 1 + 1 = a.
Proof.
  intros a.
  try ring.
Abort.

(** What's going wrong here is that [nat] is really only a semi-ring, not a
ring. That is, [nat] doesn't satisfy the axioms about negation.  Why?  Remember
that the natural numbers stop at [0]; we don't get any negative numbers. So if
[a] is [0] in the above theorem, [a-1] actually evaluates to [0] rather than
[-1]. *)

Compute 0-1.  (* 0 : nat *)

(** If we want to reason about the integers instead of the natural numbers, we
can use a library called [ZArith] for that.  The name comes from the fact that
[Z] is used in mathematics to denote the integers. *)

Require Import ZArith.
Open Scope Z_scope.

(** The [Open Scope] command causes the [ZArith] library's scope to be used to
resolve names, hence [+] becomes the operator on [Z] instead of on [nat], as
does [-], etc. *)

Compute 0-1.  (* -1 : Z *)

(** Now we can prove the theorem from before. *)

Theorem sub_add_1 : forall a : Z, a - 1 + 1 = a.
Proof.
  intros a. ring.
Qed.

(** Before going on, let's close the [Z] scope so that the operators go back to
working on [nat], as usual. *)

Close Scope Z_scope.

Compute 0-1.  (* 0 : nat *)

(** Coq also provides implementations of the rational numbers as a field, as
well as the real numbers as a field.  To get the [field] tactic, we first need
to load the [Field] library. *)

Require Import Field.

(** The rational numbers are provided in a couple different Coq libraries; the
one we'll use here is [Qcanon].  In mathematics, [Q] denotes the rational
numbers, and [canon] indicates that the numbers are stored in a _canonical
form_---that is, as simplified fractions. For example, [Qcanon] would represent
[2/4] as [1/2], eliminating the common factor of [2] from the numerator and the
denominator.  (The [QArith] library provides rational numbers that are not in
canonical form.) *)



Require Import Qcanon.
Open Scope Qc_scope.

Theorem frac_qc: forall x y z : Qc, z <> 0 -> (x + y) / z = x / z + y /z.
Proof.
  intros x y z z_not_0.
  field. assumption.
Qed.

Close Scope Qc_scope.

(** The real numbers are provided in the [Reals] library.  Here's that same
theorem again. *)

Module RealExample.

(** This code is in its own module for an annoying reason: [Reals] redefines its
own [nil], which will interefere with the examples want to give further below in
this file with lists. *)

Require Import Reals.
Open Scope R_scope.

Theorem frac_r : forall x y z, z <> 0 -> (x + y) / z = x / z + y /z.
Proof.
  intros x y z z_not_0.
  field. assumption.
Qed.

(** The assumption that [z <> 0] was needed in the above theorems to avoid
division by zero.  If we omitted that assumption, the [field] tactic would leave
us with an unprovable subgoal, as in the proof below. *)

Theorem frac_r_broken : forall x y z, (x + y) / z = x / z + y /z.
Proof.
  intros x y z.
  field.
Abort.

Close Scope R_scope.
End RealExample.

(**

(**********************************************************************)

** Induction principles

When we studied the Curry-Howard correspondence, we learned that proofs
correspond to programs.  That correspondence applies to inductive proofs
as well, and as it turns out, inductive proofs correspond to recursive
programs.  Intuitively, that's because an inductive proof involves
an inductive hypothesis---which is an instance of the theorem that
is being proved, but applied to a smaller value.  Likewise, recursive
programs involve recursive calls---which are like another instance
of the function that is already being evaluated, but on a smaller value.

To get a more concrete idea of what this means, let's look at the proof
value (i.e., program) that Coq produces for our original inductive
proof in these notes:
*)

Check app_nil.

Print app_nil.

(**
Coq responds:
<<
app_nil =
fun (A : Type) (lst : list A) =>
list_ind (fun lst0 : list A => lst0 ++ nil = lst0) eq_refl
  (fun (h : A) (t : list A) (IH : t ++ nil = t) =>
   eq_ind_r (fun l : list A => h :: l = h :: t) eq_refl IH) lst
     : forall (A : Type) (lst : list A), lst ++ nil = lst
>>

That's dense, but let's start picking it apart.  First, we see that [app_nil] is
a function that takes in two arguments: [A] and [lst].  Then it immediately
applies another function named [list_ind].  That function was defined for us in
the standard library, and it's what "implements" induction on lists.  Let's
check it out: *)

Check list_ind.

(**
Coq responds:
<<
list_ind
     : forall (A : Type) (P : list A -> Prop),
       P nil ->
       (forall (a : A) (l : list A), P l -> P (a :: l)) ->
       forall l : list A, P l
>>

We call [list_ind] the _induction principle_ for lists.  It is a proposition
that says, intuitively, that induction is a valid reasoning principle for lists.
In more detail, it takes these arguments:

- [A], which is the type of the list elements.

- [P], which is the property to be proved by induction.  For example,
  the property being proved in [app_nil] is
  [fun (lst: list A) => lst ++ nil = lst].

- [P nil], which is a proof that [P] holds of the empty list.  In other words,
  a proof of the base case.

- A final argument of type [forall (a : A) (l : list A), P l -> P (a :: l)].
  This is the proof of the inductive case.  It takes an argument [a],
  which is the head of a list, [l], which is the tail of a list, and
  a proof [P l] that [P] holds of [l].  So, [P l] is the inductive
  hypothesis.  The output is of type [P (a :: l)], which is a proof
  that [P] holds of [a::l].

Finally, [list_ind] returns a value of type [forall l : list A, P l],
which is a proof that [P] holds of all lists.

Ok, so that's the type of [list_ind]: a proposition asserting that
if you have a proof of the base case, and a proof of the inductive
case, you can assemble those to prove that a property holds of a list.
Next, what's the _value_ of [list_ind]?  In other words, what's the
proof that [list_ind] itself is actually a true proposition?
*)

Print list_ind.



(**
Coq responds:
<<
list_ind = 
fun (A : Type) (P : list A -> Prop) (f : P [])
  (f0 : forall (a : A) (l : list A), P l -> P (a :: l)) =>
fix F (l : list A) : P l :=
  match l as l0 return (P l0) with
  | [] => f
  | y :: l0 => f0 y l0 (F l0)
  end
     : forall (A : Type) (P : list A -> Prop),
       P [] ->
       (forall (a : A) (l : list A), P l -> P (a :: l)) ->
       forall l : list A, P l
...
>>

Before we look at [list_ind]'s actual implementation, let's look at our own
equivalent implementation that is easier to read: *)

Fixpoint my_list_ind
  (A : Type)
  (P : list A -> Prop)
  (baseCase : P nil)
  (inductiveCase : forall (h : A) (t : list A), P t -> P (h::t))
  (lst : list A)
  : P lst
:=
  match lst with
  | nil => baseCase
  | h::t => inductiveCase h t
              (my_list_ind A P baseCase inductiveCase t)
  end.

(** The arguments to [my_list_ind] are the same as the arguments to [list_ind]:
an element type, a property to be proved, a proof of the base case, and a proof
of the inductive case.  Then [my_list_ind] takes an argument [lst], which is
the list for which we want to prove that [P] holds.  Finally, [my_list_ind]
returns that proof specifically for [lst].

The body of [my_list_ind] constructs the proof that [P] holds of [lst].
It does so by matching against [lst]:

- If [lst] is empty, then [my_list_ind] returns the proof of the base case.

- If [lst] is [h::t], then [my_list_ind] returns the proof of the inductive
  case.  To construct that proof, it applies [inductiveCase] to [h] and [t] as
  the head and tail.  But [inductiveCase] also requires a final argument, which
  is the proof that [P] holds of [t].  To construct that proof, [my_list_ind]
  calls itself recursively on [t].

That recursive call is exactly why we said that inductive proofs are recursive
programs.  The inductive proof needs evidence that the inductive hypothesis
holds of the smaller list, and recursing on that smaller list produces the
evidence.

It's not immediately obvious, but [my_list_ind] is almost just [fold_right].
Here's how we could implement [fold_right] in Coq, with a slightly different
argument order than the same function in OCaml: *)

Fixpoint my_fold_right
  {A B : Type}
  (init : B)
  (f : A -> B -> B)
  (lst : list A)
:=
  match lst with
  | nil => init
  | h::t => f h (my_fold_right init f t)
  end.

(** Now compare the body of [my_fold_right] with [my_list_rect]:

<<
my_fold_right's body:

  match lst with
  | nil => init
  | h::t => f h (my_fold_right init f t)
  end.

my_list_ind's body:

  match lst with
  | nil => baseCase
  | h::t => inductiveCase h t (my_list_ind A P baseCase inductiveCase t)
  end.
>>

Both match against [lst].  If [lst] is empty, both return an initial/base-case
value.  If [lst] is non-empty, both recurse on the tail, then pass the result of
the recursive call to a function ([f] or [inductiveCase]) that combines that
result with the head.  The only essential difference is that [f] does not take
[t] directly as an input, whereas [inductiveCase] does.

So there you have it:  induction over a list is really just folding over the
list, eventually reaching the empty list and returning the proof of the base
case for it, then working the way back up the call stack, assembling an
ever-larger proof for each element of the list.  #<b>#An inductive proof is a
recursive program.#</b>#

Going back to the actual definition of [list_ind], here it is: *)

Print list_ind.

(** Coq responds:
<<
list_rect =
fun (A : Type) (P : list A -> Type) (f : P nil)
  (f0 : forall (a : A) (l : list A), P l -> P (a :: l)) =>
fix F (l : list A) : P l :=
  match l as l0 return (P l0) with
  | nil => f
  | y :: l0 => f0 y l0 (F l0)
  end
     : forall (A : Type) (P : list A -> Type),
       P nil ->
       (forall (a : A) (l : list A), P l -> P (a :: l)) ->
       forall l : list A, P l
>>

That uses different syntax, but it ends up defining the same function as
[my_list_ind].

Whenever you define an inductive type, Coq automatically generates the induction
principle and recursive function that implements it for you. For example, we
could define our own lists: *)

Inductive mylist (A:Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.

(** Coq automatically generates [mylist_ind] for us: *)

Print mylist_ind.

(**

(**********************************************************************)

** Extraction

Coq makes it possible to _extract_ OCaml code (or Haskell or Scheme) from
Coq code.  That makes it possible for us to

- write Coq code,
- prove the Coq code is correct, and
- extract OCaml code that can be compiled and run more efficiently
  than the original Coq code.

Let's first prove that a tail recursive factorial is equivalent to the non-tail-recursive one, and then extract the code for the tail recursive factorial.

*)

Fixpoint fact (n:nat) : nat :=
  match n with
  | 0 => 1
  | S k => n * fact k
  end.

Fixpoint fact_tail_rec' (n : nat) (acc: nat) : nat :=
  match n with
  | 0 => acc
  | S k => fact_tail_rec' k (acc * n)
  end.

Definition fact_tail_rec (n : nat) := fact_tail_rec' n 1.

(**

We need to prove an intermediate lemma about [fact_tail_rec'] for the proof of our main theorem to go through.

*)

Lemma fact_tail_rec_lem : forall n acc,
  fact_tail_rec' n acc = acc * fact_tail_rec' n 1.
Proof.
  intros n.
  induction n.
  - intro acc. simpl. ring.
  - intro acc. simpl (fact_tail_rec' (S n) 1). rewrite IHn. 
    simpl. rewrite IHn. ring.
Qed.

(**

In the above proof, the [simpl] tactic is applied with a specific pattern only on which simplification occurs. This is done so that the subsequent [rewrite] tactic does not pick the wrong term to rewrite. Try changing [simpl (fact_tail_rec' (S n) 1)] to [simpl] and make the proof go through.


Now we are ready to prove our main theorem. The proof involves induction on the input and an application of the lemma [fact_tail_rec_lem] that we had proved.

*)

Theorem fact_tail_rec_ok : forall n, fact n = fact_tail_rec n.
Proof.
  unfold fact_tail_rec.
  induction n.
  - simpl. trivial.
  - simpl. rewrite fact_tail_rec_lem. rewrite <- IHn. ring.
Qed.

(**

Let's extract [fact_tail_rec] as an example.

*)

Require Import Extraction.
Extraction Language OCaml.
Extraction "/tmp/fact.ml" fact_tail_rec.

(**

That produces the following file:

<<

type nat =
| O
| S of nat

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

(** val fact_tail_rec' : nat -> nat -> nat **)

let rec fact_tail_rec' n acc =
  match n with
  | O -> acc
  | S k -> fact_tail_rec' k (mul acc n)

(** val fact_tail_rec : nat -> nat **)

let fact_tail_rec n =
  fact_tail_rec' n (S O)

>>

As you can see, Coq has preserved the [nat] type in this extracted
code.  Unforunately, computation on natural numbers is not efficient.
(Addition requires linear time; multiplication, quadratic!)

We can direct Coq to extract its own [nat] type to OCaml's [int]
type as follows:

*)

Extract Inductive nat =>
  int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inlined Constant Init.Nat.mul => "( * )".

(**
The first command says to

- use [int] instead of [nat] in the extract code,
- use [0] instead of [O] and [succ] instead of [S]
  (the [succ] function is in [Pervasives] and is [fun x -> x + 1]), and
- use the provided function to emulate pattern matching over the type.

The second command says to use OCaml's integer [( * )] operator instead of
Coq's natural-number multiplication operator.

After issuing those commands, the extraction looks cleaner:

*)

Extraction "/tmp/fact.ml" fact_tail_rec.

(**
<<

(** val fact_tail_rec' : int -> int -> int **)

let rec fact_tail_rec' n acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> acc)
    (fun k -> fact_tail_rec' k (( * ) acc n))
    n

(** val fact_tail_rec : int -> int **)

let fact_tail_rec n =
  fact_tail_rec' n (succ 0)

>>

There is, however, a tradeoff.  The original version we extracted worked
(albeit inefficiently) for arbitrarily large numbers without any error.
But the second version is subject to integer overflow errors.  So the
proofs of correctness that we did for [fact_tail_rec] are no longer completely
applicable:  they hold only up to the limits of the types we subsituted
during extraction.

Do we truly care about the limits of machine arithmetic?  Maybe, maybe not.
For sake of this little example, we might not.  If we were verifying
software to control the flight dynamics of a space shuttle, maybe we
would.  The Coq standard library does contain a module 31-bit
integers and operators on them, which we could use if we wanted to
precisely model what would happen on a particular architecture.

*)

(**

(**********************************************************************)

** Summary

Coq excels as a proof assistant when it comes to proof by induction.  Whenever
we define an inductive type, Coq generates an induction principle for us
automatically.  That principle is really a recursive program that knows how to
assemble evidence for a proposition, given the constructors of the inductive
type.  The [induction] tactic manages the proof for us, automatically figuring
out what the base case and the inductive case, and automatically generating the
inductive hypothesis.

** Terms and concepts

- append
- base case
- field
- [fix]
- [Fixpoint]
- induction
- induction principle
- inductive case
- inductive hypothesis
- lemma
- Peano natural numbers
- [Prop] vs [bool]
- ring
- searching for library theorems
- semi-ring
- syntactically smaller restriction on recursive calls

** Tactics

- [field]
- [induction]
- [rewrite]
- [ring]
- tacticals: [try]

** Further reading

- _Software Foundations, Volume 1: Logical Foundations_.
  #<a href="https://softwarefoundations.cis.upenn.edu/lf-current/toc.html">
  Chapter 2 through 4: Induction, Lists, Poly</a>#.

- _Interactive Theorem Proving and Program Development_.
  Chapters 6 through 10. Available
  #<a href="https://newcatalog.library.cornell.edu/catalog/10131206">
  online from the Cornell library</a>#.

*)