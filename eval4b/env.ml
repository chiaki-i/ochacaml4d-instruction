type 'a t = 'a list

let empty = []

(* exceptions *)
exception UnboundVariable

(* off_set : string -> xs -> int *)
let off_set x xs =
  let rec loop xs n = match xs with
      [] -> raise UnboundVariable
    | first :: rest -> if x = first then n else loop rest (n + 1)
  in
  loop xs 0
