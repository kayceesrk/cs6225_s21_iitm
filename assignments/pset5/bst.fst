module Bst

type tree =
  | Leaf : tree
  | Node : n:int -> tree -> tree -> tree

val tree_mem : int -> tree -> Tot bool
let rec tree_mem x t =
  match t with
  | Leaf -> false
  | Node n t1 t2 -> x = n || tree_mem x t1 || tree_mem x t2

val tree_forall : p:(int -> Tot bool) -> t:tree ->
            Tot (r:bool{r <==> (forall x. tree_mem x t ==> p x)})
let rec tree_forall p t =
  match t with
  | Leaf -> true
  | Node n t1 t2 -> p n && tree_forall p t1 && tree_forall p t2

let tree_lt n = tree_forall (fun v -> v < n)
let tree_gt n = tree_forall (fun v -> v > n)

val bst : tree -> Tot bool
let rec bst t =
  match t with
  | Leaf -> true
  | Node n lt rt ->
    bst lt && tree_lt n lt &&
    bst rt && tree_gt n rt

let singleton n = Node n Leaf Leaf

val insert :
  x:int -> t:tree{bst t} ->
  Tot (r:tree{bst r /\
     (forall y. tree_mem y r <==> (tree_mem y t \/ x = y))})
let rec insert x t =
  match t with
  | Leaf -> singleton x
  | Node n t1 t2 -> if x = n then      t
                    else if x < n then Node n (insert x t1) t2
                    else               Node n t1 (insert x t2)

val tree_max : tree -> Tot int
(* TODO (10 points): Define the function [tree_max] (it finds the largest element in a tree)
 * and refine its type so that the function delete (below, in comments)
 * type-checks.
 *
 * Observe that [tree_max] is a total function that returns an int. Hence, it
 * cannot accept [Leaf] as an argument. In F*, whenever you define a data type, you get boolean discriminators for constructors for free. For example: *)

val root1 : tree -> Tot (option int)
let root1 t = match t with
  | Leaf -> None
  | Node v _ _ -> Some v

val root2 : t:tree{Node? t} -> Tot int
let root2 t = match t with
  | Node v _ _ -> v

(* In the above, [Node?] is a implicitly defined function of type [tree -> bool]
   which returns [true] if the given tree is not a [Leaf]. Since we statically
   know that the given tree is not a [Leaf], we have no [Leaf] case in [root2].
   You may want to use [Node?] in your definition of [tree_max] *)

(*
val delete : x:int -> t:tree{bst t} ->
  Tot (r:tree{bst r /\ not (tree_mem x r)  /\
              (forall y. x <> y ==> (tree_mem y t = tree_mem y r))}) (decreases t)
let rec delete x t = match t with
  | Leaf -> Leaf
  | Node n t1 t2 -> if n = x then
                      match t1, t2 with
                      | Leaf, Leaf -> Leaf
                      | _   , Leaf -> t1
                      | Leaf, _    -> t2
                      | _          -> let y = tree_max t1 in
                                     Node y (delete y t1) t2
                    else if x < n then Node n (delete x t1) t2
                                  else Node n t1 (delete x t2)
*)

(* Once you get the definition of [tree_max] right, all of the following lemmas
   come for free (including the commented out ones) *)

val insert_member : t:tree -> v:int -> Lemma (requires (bst t))
                                    (ensures (tree_mem v (insert v t)))
let insert_member tr v = ()

val insert_ok : t:tree -> v:int -> Lemma (requires (bst t))
                                     (ensures (bst (insert v t)))
let insert_ok tr v = ()

(*
val delete_ok : t:tree -> v:int -> Lemma (requires (bst t))
                                     (ensures (bst (delete v t)))
let delete_ok tr v = ()

val delete_member : t:tree -> v:int -> Lemma (requires (bst t))
                                         (ensures (not (tree_mem v (delete v t))))
let delete_member tr v = ()
*)

assume val tree_max' : t:tree{Node? t} -> Tot int

val delete' : x : int -> t:tree -> Tot tree (decreases t)
let rec delete' x t = match t with
  | Leaf -> Leaf
  | Node n t1 t2 -> if n = x then match (t1, t2) with
                      | (Leaf, Leaf) -> Leaf
                      | (_, Leaf) -> t1
                      | (Leaf, _) -> t2
                      | _ ->
                          let y = tree_max' t1 in
                            Node y (delete' y t1) t2
                    else if x < n then Node n (delete' x t1) t2
                         else Node n t1 (delete' x t2)

(* TODO (20 points): Give an extrinsic proof showing the correctness of
   [delete'] (i.e. show the same properties that were shown for [delete])

	 Hint: in the process you need to write the function [tree_max'] and give an
	 extrinsic proof of correctness for it. You should delete the [assume val
	 tree_max'] when doing that. *)
