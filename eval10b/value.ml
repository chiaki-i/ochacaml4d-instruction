open Syntax

(* Definitional interpreter for λ-calculus with 4 delimited continuation operations : eval1 *)

(* Value *)
type v = VNum of int
       | VFun of i list * v list
       | VContS of c * s * t
       | VContC of c * s * t
       | VEmpty

and c = (i list * v list) list

and i = IPushmark
      | INum of int | IAccess of int | IOp of op
      | IApply | IReturn
      | ICur of i list | IGrab of i list
      | IShift of i list | IControl of i list
      | IShift0 of i list | IControl0 of i list
      | IReset of i list

and s = v list

and t = TNil | Trail of h

and h = Hold of c * s
      | Append of h * h

and m = MNil | MCons of (c * s * t) * m

(* to_string : v -> string *)
let rec to_string value = match value with
    VNum (n) -> string_of_int n
  | VFun (_) -> "<VFun>"
  | VContS (_) -> "<VContS>"
  | VContC (_) -> "<VContC>"
  | VEmpty -> "<ε>"

(* s_to_string : s -> string *)
let rec s_to_string s =
  "[" ^
  begin match s with
    [] -> ""
  | first :: rest ->
    to_string first ^
    List.fold_left (fun str v -> str ^ "; " ^ to_string v) "" rest
  end
  ^ "]"

(* Value.print : v -> unit *)
let print exp =
  let str = to_string exp in
  print_string str

(* i_to_string : i -> string *)
let rec i_to_string inst = match inst with
    IPushmark -> "Pushmark"
  | INum (n) -> "Num (" ^ string_of_int n ^ ")"
  | IAccess (n) -> "Access (" ^ string_of_int n ^ ")"
  | IOp (op) ->
    let s = match op with
        Plus -> "+" | Minus -> "-" | Times -> "*" | Divide -> "/" in
    "Op (" ^ s ^ ")"
  | IApply -> "Apply"
  | IReturn -> "Return"
  | ICur (is) -> "Cur (" ^ i_list_to_string is ^ ")"
  | IGrab (is) -> "Grab (" ^ i_list_to_string is ^ ")"
  | IShift (is) -> "Shift (" ^ i_list_to_string is ^ ")"
  | IControl (is) -> "Control (" ^ i_list_to_string is ^ ")"
  | IShift0 (is) -> "Shift0 (" ^ i_list_to_string is ^ ")"
  | IControl0 (is) -> "Control0 (" ^ i_list_to_string is ^ ")"
  | IReset (is) -> "Reset (" ^ i_list_to_string is ^ ")"

(* i_list_to_string : i list -> string *)
and i_list_to_string lst = match lst with
    [] -> "●"
  | first :: rest ->
    i_to_string first ^
    List.fold_left (fun str i -> str ^ "; " ^ i_to_string i) "" rest

(* c_to_string : c -> string *)
let c_to_string c =
  match c with
    [] -> "●"
  | (is, vs) :: rest ->
    "(" ^ i_list_to_string is ^ ", " ^ s_to_string vs ^ ")" ^
    List.fold_left (fun str (is', vs') -> str ^ " :: (" ^ i_list_to_string is' ^ ", " ^ s_to_string vs' ^ ")") "" rest

(* h_to_string : h -> string *)
let rec h_to_string h =
  match h with
    Hold (c, s) -> "(" ^ c_to_string c ^ ", " ^ s_to_string s ^ ")"
  | Append (h1, h2) -> h_to_string h1 ^ " @ " ^ h_to_string h2

(* t_to_string : t -> string *)
let t_to_string t =
  match t with
    TNil -> "●"
  | Trail (h) -> h_to_string h

(* m_to_string : m -> string *)
let rec m_to_string m =
  match m with
    MNil -> "●"
  | MCons ((c, s, t), m') -> "((" ^ c_to_string c ^ ", " ^ s_to_string s ^ ", " ^ t_to_string t ^ "), " ^ m_to_string m' ^ ")"

(* print_machine : c -> s -> t -> m -> unit *)
let print_machine c s t m  =
  let inst = match c with
      [] -> "●"
    | (is, _) :: _ -> i_list_to_string is in
  let env = match c with
      [] -> "●"
    | (_, vs) :: _ -> s_to_string vs in
  let arg = s_to_string s in
  let ret = match c with
      [] -> "●"
    | _ :: rest -> c_to_string rest in
  let trail = t_to_string t in
  let meta = m_to_string m in
  print_endline ("i: " ^ inst);
  print_endline ("e: " ^ env);
  print_endline ("s: " ^ arg);
  print_endline ("r: " ^ ret);
  print_endline ("t: " ^ trail);
  print_endline ("m: " ^ meta);
  print_endline "--------------------"
