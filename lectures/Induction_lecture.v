(**
* Induction in Coq
*)

Require Import List.
Import ListNotations.

(**********************************************************************)

(** Recursive functions *)

Fixpoint append {A : Type} (lst1 : list A) (lst2 : list A) :=
  match lst1 with
  | nil => lst2
  | h::t => h :: (append t lst2)
  end.

Theorem nil_app : forall (A:Type) (lst : list A),
  [] ++ lst = lst.
Proof.
  intros A lst.
  simpl.
  trivial.
Qed.

Theorem app_nil : forall (A:Type) (lst : list A),
  lst ++ [] = lst.
Proof.
  intros A lst. 
  simpl. (* cannot simplify *)
  destruct lst. (* case analysis *)
  - trivial.
  - simpl.  (* can't proceed *)
Abort.

(* Case analysis doesn't work. We need to apply _induction_ *)














(**********************************************************************)

(** Induction on lists

Here's the structure of a proof by induction on a list:

<<
Theorem.  For all lists lst, P(lst).

Proof.  By induction on lst.

For the base case, 

Case:  lst = []
Show:  P([])

For the inductive case, 

Case:  lst = h::t
IH:    P(t)
Show:  P(h::t)

QED.
>>

Here's how that proof could be written:

<<
Theorem:  for all lists lst, lst ++ [] = lst.

Proof:  by induction on lst.
P(lst) = lst ++ [] = lst.

Case:  lst = []
Show:
  P([])
= [] ++ [] = []
= [] = []

Case:  lst = h::t
IH: P(t) = (t ++ [] = t)
Show
  P(h::t)
= (h::t) ++ [] = h::t     // by definition of P
= h::(t ++ []) = h::t     // by definition of ++
= h::t = h::t             // by IH

QED
>>

In Coq, we could prove that theorem as follows:
*)

Theorem app_nil : forall (A:Type) (lst : list A),
  lst ++ nil = lst.
Proof.
 intros A lst. 
 induction lst. (* new tactic *)
- simpl. trivial.
- simpl.
  rewrite -> IHlst. (* new tactic *)
  trivial.
Qed.

Print app_nil.

Check list_ind.

Theorem app_assoc : forall (A:Type) (l1 l2 l3 : list A),
  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
  intros A l1 l2 l3.
  induction l1.
  - simpl. trivial.
  - simpl. rewrite <- IHl1. trivial.
Qed.

























(**
(**********************************************************************)

** Induction on natural numbers

Prove [0 + 1 + ... + n = n * (n+1) / 2].

The structure of a proof by induction on the naturals is as follows:

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

In Coq, natural numbers are encoded using Peano numerals, credited to Giuseppe Peano (1858-1932).

<<
type nat = O | S of nat
>>

- 0 is [O]
- 1 is [S O]
- 2 is [S (S O)]
- 3 is [S (S (S O))]
- etc.

The Coq definition of [nat] is much the same:
*)

Print nat.

(** We can even write computations using those constructors: *)

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

Let's get back to our goal. To prove [1+2+...+n = n * (n+1) / 2].

In Coq, it will turn out to be surprisingly tricky...





























(**********************************************************************)

** Recursive functions, revisited

Here's a first attempt at defining [sum_to] *)

Fail Fixpoint sum_to (n:nat) : nat :=
  if n = 0 then 0 else n + sum_to (n-1).
(* [Fail] keyword -- expect definition to fail *)

(**
[=] returns [Prop]. We need something that returns [bool]. Such an operator is defined in the [Arith] library for us: 
*)

Require Import Arith.

Locate "=?".
Check Nat.eqb.


Fail Fixpoint sum_to (n:nat) : nat :=
  if n =? 0 then 0 else n + sum_to (n-1).

(** A digression. Let's look at a different recursive function---one that implements an infinite loop: *)

Fail Fixpoint inf (x:nat) : nat := inf x.

(**
  + Coq does not permit any infinite loops

Consider [inf] in OCaml:

<<
# let rec inf x = inf x
val inf : 'a -> 'b = <fun>
>>

  + Type ['a -> 'b] would be [A -> B] in Coq. 
  + If [A] is [True] and [B] is [False], then [inf] would be evidence for [True -> False].
  + We can derive contradiction by [inf I]!!!
  
Can't we just rule out infinite programs?

  + But _halting problem_ is undecidable:  we can't write a program that precisely determines whether another program will terminate.
  + Coq goes for imprecise solution -- recursive calls must be on syntactically smaller term.
    - [n] syntactically smaller than [n+1]
    - [n-1] syntactically larger than [n].
*)

Fail Fixpoint sum_to (n:nat) : nat :=
  if n =? 0 then 0 else n + sum_to (n-1).

Fixpoint sum_to (n:nat) : nat :=
  match n with
  | 0 => 0
  | S k => n + sum_to k
  end.




































(**********************************************************************)

(** Inductive proof of the summation formula

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
  induction n.
  - trivial.
  - simpl. rewrite -> IHn.
Abort.

(** [Nat.divmod] is integer division. 

To avoid having to reason about division, multiply both sides by 2 *)

Theorem sum_sq_no_div : forall n : nat,
  2 * sum_to n = n * (n+1).
Proof.
  intros n.
  induction n.
  - trivial.
  - simpl.
Abort.

(** [simpl] is too agressive! Let's define a helper _lemma. *)

(* + Natural numbers with [+] and [*] form a _ring_
     - https://en.wikipedia.org/wiki/Ring_(mathematics)
   + Coq has good support for proofs on rings
*)

Lemma sum_helper : forall n : nat,
  2 * sum_to (S n) = 2 * (S n) + 2 * sum_to n.
Proof.
  intros n. simpl.
  ring. (* new tactic *)
Qed.

(** Now that we have our helper lemma, we can use it to prove the theorem: *)

Theorem sum_sq_no_div : forall n : nat,
  2 * sum_to n = n * (n+1).
Proof.
  intros n.
  induction n.
  - trivial.
  - rewrite -> sum_helper.
    rewrite -> IHn.
    ring.
Qed.

(** 

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
whereas we have [b * a / b].  The problem is that the two sides of the
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
*)

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

Theorem fact_tail_rec_ok' : forall n, fact n = fact_tail_rec n.
Proof.
  unfold fact_tail_rec.
  induction n.
  - simpl. trivial.
  - simpl. rewrite IHn.
Abort.

(**

We need to prove an intermediate lemma about [fact_tail_rec'] for the proof of our main theorem to go through.

*)

Lemma fact_tail_rec_lem : forall n acc,
  fact_tail_rec' n acc = acc * fact_tail_rec' n 1.
Proof.
  intro n.
  induction n.
  - intro acc. simpl. ring.
  - intro acc. simpl. 
    rewrite IHn. 
    rewrite (IHn (S (n + 0))). (* to get the cirrect term to reduce *)
    ring.
Qed.

(**

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
