module Pset11

open FStar.All
open FStar.Ref

val lookup : list (int * int) -> int -> option int
let rec lookup l k =
  match l with
  | [] -> None
  | (k',v)::xs -> if k = k' then Some v else lookup xs k

val memo : int (* Give a type that makes the program type check. No need to
                capture the details of the algorithm in the type. Just some
                type that passes type checking should do. (10 points). *)
let memo f =
  let cache = alloc [] in
  fun k ->
    match lookup !cache k with
    | None ->
        let v = f k in
        cache := (k,v)::!cache;
        v
    | Some v -> v

noeq type node : Type =
  | Node : ref (option node) -> node

(* This function takes two nodes and makes them point to each other. Give a
   type that fully captures the details of what's going on i.e, full functional
   specifiction. You may make reasonable assumption about the precondition. Ask
   youself whether you need any? (20 points) *)
val cycle : n1:node -> n2: node -> ST unit (fun _ -> True (* FILL IN *)) (fun _ _ _ -> True (* FILL IN *))
let cycle n1 n2 =
  let Node r1 = n1 in
  let Node r2 = n2 in
  r2 := Some n1;
  r1 := Some n2
