module Fib

(** TODO (5 points): Prove that tail recursive fibonacci is equivalent to the non-tail recursive
    one. The definition of tail recursive fibonacci function is the same as what
		you had seen in the mid-term. *)

val fib : nat -> Tot nat
let rec fib n =
  if n < 2 then 1 else fib (n-1) + fib (n-2)

val fib_tail_rec : nat -> Tot nat
let fib_tail_rec n = 1

val fib_same : n:nat -> Lemma (ensures (fib n = fib_tail_rec n))
let rec fib_same n = 1
