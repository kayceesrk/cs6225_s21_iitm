(**
* PSet3: Induction in Coq (240 points)
*)

Require Import List Arith.

(**********************************************************************)

(* Exercise: app_assoc coq [10 points].
   In Coq, the list append operator is written [++]. Complete the following
   proof by induction, which shows that application is associative.
   Hint:  the solution is in the lecture slides. *)

Theorem app_assoc : forall (A:Type) (l1 l2 l3 : list A),
  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
  intros A l1 l2 l3.
  induction l1 as [ | h t IH].
  (* FILL IN, and change [Abort] to [Qed]. *)
Abort.

(**********************************************************************)

(* Exercise: app_assoc math [20 points].

Prove that the OCaml [@] operator is also associative.  Your answer should
be a mathematical proof, not a Coq proof.  We have supplied part of the
proof for you.

Theorem:  for all lists lst1, lst2, and lst3,
  lst1 @ (lst2 @ lst3) = (lst1 @ lst2) @ lst3.

Proof:  by induction on lst1.
The property being proved is:
P(l) = FILL IN

Case:  lst1 = []
Show:  FILL IN

Case: lst1 = h::t
IH:  FILL IN
Show:  FILL IN

QED

*)

(**********************************************************************)

(* Exercise: rev_append math [30 points].

Prove the following theorem, which shows how list reversal distributes
over list append.

Theorem: for all lists lst1 and lst2,
  rev (lst1 @ lst2) = rev lst2 @ rev lst1.

Recall that [rev] is defined as follows:
<<
let rec rev = function
  | [] -> []
  | h::t -> rev t @ [h]
>>

Your answer should be a mathematical proof, not a Coq proof. In the inductive
case, you will need the lemma proved above saying that append is associative. In
the base case, you will need this lemma:

Lemma:  for all lists lst, lst @ [] = lst.
Proof:  given in lecture.

Here, again, is the theorem you should prove:

Theorem: for all lists lst1 and lst2,
  rev (lst1 @ lst2) = rev lst2 @ rev lst1.

Proof:  FILL IN

*)

(**********************************************************************)

(* Exercise: rev_append coq [30 points].

Now prove the same theorem as the previous exercise, but in Coq.
The Coq list reversal function [rev] is defined in the standard
library for you.  Use the mathematical proof you gave above
as a guide.  For the base case, you will need the lemma [app_nil]
that we proved in lecture; we've inserted the code for it below.
You can use that lemma in your own proof with the [rewrite] tactic.
*)

Lemma app_nil : forall (A:Type) (lst : list A),
  lst ++ nil = lst.
Proof.
  intros A lst.
  induction lst as [ | h t IH].
  - trivial.
  - simpl. rewrite -> IH. trivial.
Qed.

Theorem rev_append : forall (A:Type) (lst1 lst2 : list A),
  rev (lst1 ++ lst2) = rev lst2 ++ rev lst1.
Proof.
  (* FILL IN, and change [Abort] to [Qed] *)
Abort.

(**********************************************************************)

(* Exercise: rev involutive [30 points].

Prove that [rev] is _involutive_, meaning that it is its own inverse. That is,
[rev (rev lst) = lst].

Hint:  for the inductive case, there is a lemma that has already been proved in
this lab that you will find very helpful.  Part of this exercise is figuring out
which lemmma that is.
*)

Theorem rev_involutive : forall (A:Type) (lst : list A),
  rev (rev lst) = lst.
Proof.
  (* FILL IN, and change [Abort] to [Qed] *)
Abort.

(**********************************************************************)

(* Exercise: app_length [Optional].
Prove the following theorem in Coq.
*)

(*
Theorem app_length : forall (A:Type) (l1 l2 : list A),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  (* FILL IN, and change [Abort] to [Qed] *)
Abort.
*)

(**********************************************************************)

(* Exercise: rev_length [Optional].
Prove the following theorem in Coq.

Hint: previous exercise(s) as lemma, and the [ring] tactic.
*)

(*
Theorem app_rev : forall (A:Type) (lst : list A),
  length (rev lst) = length lst.
Proof.
  (* FILL IN, and change [Abort] to [Qed] *)
Abort.
*)

(**********************************************************************)

(* INDUCTION ON BINARY TREES *)

(* Here is a Coq type for binary trees: *)
Inductive tree (A : Type) : Type :=
  | Leaf : tree A
  | Node : tree A -> A -> tree A -> tree A.

(* The following commands cause the [A] argument to
   be implicit to the [Leaf] and [Node] constructors. *)
   Arguments Leaf [A].
   Arguments Node [A] _ _ _.

(* The equivalent OCaml type would be:
<<
type 'a tree =
  | Leaf
  | Node of 'a tree * 'a * 'a tree
>>
*)

(* The _reflection_ operation swaps the left and right
   subtrees at every node. *)
Fixpoint reflect {A : Type} (t : tree A) :=
  match t with
  | Leaf => Leaf
  | Node l v r => Node (reflect r) v (reflect l)
  end.

(* The equivalent OCaml function would be:
<<
let rec reflect = function
  | Leaf -> Leaf
  | Node (l,v,r) -> Node (reflect r, v, reflect l)
>>
*)

(* A proof by induction on a binary tree has the following structure:

Theorem:  For all binary trees t, P(t).

Proof: by induction on t.

Case: t = Leaf
Show: P(Leaf)

Case: t = Node(l,v,r)
IH1:  P(l)
IH2:  P(r)
Show:  P(Node(l,v,r))

QED

Note that we get _two_ inductive hypotheses in the inductive
case, one for each subtree.
*)

(**********************************************************************)

(* Exercise: tree_ind [20 points].
Explain the output of the following command in your own words, relating it to
the proof structure given above for induction on binary trees.
Hint: read the notes on induction principles.
*)

Check tree_ind.

(**********************************************************************)

(* Exercise: reflect_involutive math [30 points].
Prove the following theorem mathematically (not in Coq).

Theorem:  for all trees t, reflect (reflect t) = t

Proof: by induction on t.
P(t) = reflect (reflect t) = t

Case: t = Leaf
Show: FILL IN

Case: t = Node(l,v,r)
IH1: P(l) = reflect(reflect l) = l
IH2: P(r) = reflect(reflect r) = r
Show: FILL IN

QED
*)

(**********************************************************************)

(* Exercise: reflect_involutive coq [30 points].
State and prove a theorem in Coq that shows reflect is involutive.
Use your mathematical proof from the previous exercise as a guide.

Hint: the [induction] tactic expects the arguments for the inductive
case in the following order:  the left subtree, the IH for the left subtree,
the value at the node, the right subtree, and the IH for the right subtree.
*)

(*
UNCOMMENT AND COMPLETE
Theorem reflect_involutive : ...
*)

(**********************************************************************)

(* Exercise: height [40 points].

1. Write a Coq function [height] that computes the height of a binary tree.
Recall that the height of a leaf is 0, and the height of a node is 1 more than
the maximum of the heights of its two subtrees.  The standard library does
contain a [max] function that will be helpful.

2. Prove that [reflect] preserves the height of a tree.  Hint: [Nat.max_comm].

3. Write a Coq function [perfect : nat -> tree nat], such that
[perfect h] constructs the perfect binary tree of height [h], and
the value at the root is [1], and if the value at a node is [v],
then the values of its left and right subnodes are [2*v] and [2*v+1].
For example, [perfect 3] is
<<
Node (Node (Node Leaf 4 Leaf) 
           2 
           (Node Leaf 5 Leaf)) 
     1
     (Node (Node Leaf 6 Leaf) 
           3 
           (Node Leaf 7 Leaf))
>>

4. Prove that the height of [perfect h] is in fact [h].  Hint 1: induct
on [h].  Hint 2: don't introduce all the variables. Hint 3:
[Nat.max_idempotent].
*)
