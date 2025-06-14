open Syntax

(* interpreter with defunctionalized continuations: eval2st *)

(* Value *)
type v = VNum of int
       | VFun of (v -> v list -> c -> t -> m -> v)
       | VContS of c * t
       | VContC of c * t

and c = C0
      | CApp of v list * c
      | CApp1 of v * v list * c
      | CAppS0 of v list * c
      | CAppS1 of e * string list * v list * c
      | CAppS2 of e * string list * v list * c
      | COp0 of v * op * c
      | COp1 of e * string list * op * v list * c

and t = TNil | Trail of (v -> t -> m -> v)

and m = MNil | MCons of (c * t) * m

(* to_string : v -> string *)
let rec to_string value = match value with
    VNum (n) -> string_of_int n
  | VFun (_) -> "<VFun>"
  | VContS (_) -> "<VContS>"
  | VContC (_) -> "<VContC>"

(* Value.print : v -> unit *)
let print exp =
  let str = to_string exp in
  print_string str