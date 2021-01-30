module Fstar_functional

open FStar.Mul

(* Statically Checked Assertions *)

let max i1 i2 = if i1 > i2 then i1 else i2
 
let _ = assert (max 0 1 = 1)

let _ = assert (forall x y z. max x y = y && max y z = z ==>
                         max x z = z)
 
(* Recursive functions *)

val factorial: nat -> nat
let rec factorial n =
  if n = 0 then 1
  else n * (factorial (n - 1)) (* in coq [n-1] would complain *)

(* Inductive datatypes and pattern matching *)

type list (a:Type) =
  | Nil  : list a
  | Cons : hd:a -> tl:list a -> list a

val map : ('a -> 'b) -> list 'a -> list 'b
let rec map f x =
  match x with
  | Nil -> Nil
  | Cons h t -> Cons (f h) (map f t)

(* Lambdas *)

let l = map (fun x -> x + 1) (Cons 2 (Cons 1 Nil))

(******************************************************************************)

(* Refinement Types

   <<switch to slides>>
*)

(* Refinements eliminated by subtyping [nat <: int]*)
let i : int = factorial 42

let f : x:nat{x > 0} -> int = factorial

(* [factorial 0] type checks *)
let _ = factorial 0

(* But [f 0] is ill-typed *)
(* let _ = f 0 *)

(* The proof obligations are discharged by the z3 SMT solver *)

(******************************************************************************)

(* Dependent Types *)

val incr : x:int -> y:int{y > x}
let incr x = x + 1

(* The type [x:int -> y:int{y > x}] is said to be a dependent type since the type of
   the result depends on the argument value. F* automatically type checks the
   [incr] function to ensure that it satisfies the specification.

   For example, the following specification for an increment function is incorrect
   and does not type check. *)

val incr2 : x:int -> y:int{ y < x}
(* let incr2 x = x + 1 *)

(* Unlike OCaml where there can only be one type for the [incr] function, in F*
   there is a family of types that can be assigned to [incr] *)

val incr3 : x:int -> y:int{ y >= x}
let incr3 x = x + 1

val incr4 : int -> int
let incr4 x = x + 1

val incr5 : x:int{x=5} -> y:int{y=6}
let incr5 x = x + 1

(* How can you define this family? For all types [t] that belong to this family
   there exists a type [t'] such that [t' <: t] *)

val incr6 : x:int -> y:int{y=x+1}
let incr6 x = x + 1

(* Notice that the above type is the most precise type that you can give to the increment function *)

(******************************************************************************)

(* Total Functions

   <<switch to slides>>

*)

val factorial2 : nat -> Tot nat
let rec factorial2 n =
  if n = 0 then 1 else n * factorial2 (n-1)

(* What about the following type for factorial? *)

(* let factorial3 : int -> Tot int = factorial2 *)


(******************************************************************************)

(* Semantic Termination Checking

   <<switch to slides>>
*)

val ackermann: m:nat -> n:nat -> Tot nat (decreases %[m;n])
let rec ackermann m n =
  if m = 0 then n + 1
  else if n = 0 then ackermann (m - 1) 1
  else ackermann (m - 1) (ackermann m (n - 1))

val ackermann2: m:nat -> n:nat -> Tot nat
let rec ackermann2 m n =
  if m = 0 then n + 1
  else if n = 0 then ackermann2 (m - 1) 1
  else ackermann2 (m - 1) (ackermann2 m (n - 1))

(* if the [decreases] annotation were to be removed, then this program would not
   type check *)
val ackermann3: n:nat -> m:nat -> Tot nat (decreases %[m;n])
let rec ackermann3 n m =
  if m = 0 then n + 1
  else if n = 0 then ackermann3 1 (m - 1)
  else ackermann3 (ackermann3 (n - 1) m) (m-1)

(********************************************************************************)

(* Divergence

  <<switch to slides>>

*)

val factorial3 : int -> Dv int
let rec factorial3 n = if n = 0 then 1 else n * factorial3 (n-1)

type exp =
| App : exp -> exp -> exp
| Lam : nat -> exp -> exp
| Var : nat -> exp

val subst : x:nat -> e1:exp -> e2:exp -> Tot exp 
let rec subst x e1 e2 =
  match e2 with
  | Var x' -> if x = x' then e1 else Var x'
  | App e21 e22 -> App (subst x e1 e21) (subst x e1 e22)
  | Lam x' e2' -> Lam x (subst x e1 e2') (* naive implementation *)

val eval : exp -> Dv exp
let rec eval e =
  match e with
  | App (Lam x e1) e2 -> eval (subst x e2 e1)
  | App e1 e2 -> eval (App (eval e1) e2)
  | Lam x e1 -> Lam x (eval e1)
  | _ -> e

(* this loops forever *)
let loops_forever () = eval (App (Lam 0 (App (Var 0) (Var 0)))
                                 (Lam 0 (App (Var 0) (Var 0))))

(******************************************************************************)

(* Effect System

  <<switch to slides>>

*)

(* Pure code cannot call divergent code *)

(* let foo () : Tot int = incr 2 + factorial3 (-1) *)

(* Only pure code can appear in specs *)

(* type tau = x:int{x = factorial3(5)} *)

(* Divergent code can call pure code *)

let baz () : Dv int = incr 2 + factorial3 (-1)
(* In the above, there is sub-effecting in play. Identify. *)

(* <<switch to slides>> *)

(******************************************************************************)

(* Example: A simple model of access control *)

open FStar.Exn
open FStar.All
//safe-read-write

type filename = string

(** [canWrite] is a function specifying whether a file [f] can be written *)
let canWrite (f:filename) =
  match f with
    | "demo/tempfile" -> true
    | _ -> false

(** [canRead] is also a function ... *)
let canRead (f:filename) =
  canWrite f              (* writeable files are also readable *)
  || f="demo/README"       (* and so is demo/README *)

(* Only those file for which F* can statically prove that they can be read
   are allowed to be read. *)
val read  : f:filename{canRead f}  -> ML string
let read f  = FStar.IO.print_string ("Dummy read of file " ^ f ^ "\n"); f

(* Only those file for which F* can statically prove that they can be written
   are allowed to be written . *)
val write : f:filename{canWrite f} -> string -> ML unit
let write f s = FStar.IO.print_string ("Dummy write of string " ^ s ^ " to file " ^ f ^ "\n")



(** Example files *)
let passwd : filename = "demo/password"
let readme : filename = "demo/README"
let tmp    : filename = "demo/tempfile"




(** Static Checking *)
val staticChecking : unit -> ML unit
let staticChecking () =
  let v1 = read tmp in
  let v2 = read readme in
  (* let v3 = read passwd in (* invalid read, fails type-checking *) *)
  write tmp "hello!"
  (* ; write passwd "junk" // invalid write , fails type-checking *)




(** Dynamic Checking *)
exception InvalidRead
val checkedRead : filename -> ML string
let checkedRead f =
  if canRead f then read f else raise InvalidRead

val checkedWrite : filename -> string -> ML unit
exception InvalidWrite
let checkedWrite f s =
  if canWrite f then write f s else raise InvalidWrite

let dynamicChecking () =
  let v1 = checkedRead tmp in
  let v2 = checkedRead readme in
  let v3 = checkedRead passwd in (* this raises exception *)
  checkedWrite tmp "hello!";
  checkedWrite passwd "junk" (* this raises exception *)

let main = staticChecking (); dynamicChecking ()
