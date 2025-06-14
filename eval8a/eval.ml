open Syntax
open Value

(* Interpreter using combinators factored as instructions : eval8st *)

(* initial continuation *)
let idc = fun s t m -> match s with
    v :: [] ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t), m) -> c (v :: s) t m
        end
      | Trail (h) -> h v TNil m
    end
  | _ -> failwith ("idc: stack error: " ^ s_to_string s)

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* (>>) : i -> i -> i *)
let (>>) i0 i1 = fun vs c -> i0 vs (i1 vs c)

(* num : int -> i *)
let num n = fun vs c s t m -> c (VNum (n) :: s) t m

(* access : int -> i *)
let access n = fun vs c s t m -> c (List.nth vs n :: s) t m

(* operation : op -> i *)
let operation op = fun vs c (v :: v0 :: s) t m ->
  begin match (v, v0) with
      (VNum (n0), VNum (n1)) ->
      begin match op with
          Plus -> c (VNum (n0 + n1) :: s) t m
        | Minus -> c (VNum (n0 - n1) :: s) t m
        | Times -> c (VNum (n0 * n1) :: s) t m
        | Divide ->
          if n1 = 0 then failwith "Division by zero"
          else c (VNum (n0 / n1) :: s) t m
      end
    | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
  end

let cur i = fun vs c s t m ->
  c ((VFun (fun c' (v1 :: s') t' m' ->
    i (v1 :: vs) c' s' t' m')) :: s) t m

(* apply8 : v -> v -> c -> s -> t -> m -> v *)
let rec apply8 v0 v1 c s t m =
  match v0 with
    VFun (f) -> f c (v1 :: s) t m
  | VContS (c', s', t') ->
    let app_c = fun (v :: s) t m -> apply8s v c s t m in
    c' (v1 :: s') t' (MCons ((app_c, s, t), m))
  | VContC (c', s', t') ->
    let app_c = fun (v :: s) t m -> apply8s v c s t m in
    c' (v1 :: s') (apnd t' (cons (fun v t m -> app_c (v :: s) t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* apply8s : v -> v list -> c -> s -> t -> m -> v *)
and apply8s v0 c s t m = match s with
  VEmpty :: s -> c (v0 :: s) t m
| v1 :: s -> apply8 v0 v1 c s t m

(* shift : i -> i *)
let shift i = fun vs c s t m ->
  i (VContS (c, s, t) :: vs) idc [] TNil m

(* control : i -> i *)
let control i = fun vs c s t m ->
  i (VContC (c, s, t) :: vs) idc [] TNil m

(* shift0 : i -> i *)
let shift0 i = fun vs c s t m -> match m with
    MCons ((c0, s0, t0), m0) ->
    i (VContS (c, s, t) :: vs) c0 s0 t0 m0
  | _ -> failwith "shift0 is used without enclosing reset"

(* control0 : i -> i *)
let control0 i = fun vs c s t m -> match m with
    MCons ((c0, s0, t0), m0) ->
    i (VContC (c, s, t) :: vs) c0 s0 t0 m0
  | _ -> failwith "control0 is used without enclosing reset"

(* reset : i -> i *)
let reset i = fun vs c s t m ->
  i vs idc [] TNil (MCons ((c, s, t), m))

let pushmark = fun vs c s t m -> c (VEmpty :: s) t m

(* return : i *)
let return = fun vs c (v :: s) t m ->
  apply8s v c s t m

(* apply : i *)
let apply = fun vs c (v0 :: v1 :: s) t m ->
  apply8 v0 v1 c s t m

(* grab: i -> i *)
let grab i = fun vs c s t m ->
  begin match s with
    VEmpty :: s ->
    c ((VFun (fun c' (v1 :: s') t' m' ->
      i (v1 :: vs) c' s' t' m')) :: s) t m
  | v1 :: s -> i (v1 :: vs) c s t m
  | _ -> failwith "grab: stack is empty"
  end

(* f8: e -> string list -> i *)
let rec f8 e xs = match e with
    Num (n) -> num n
  | Var (x) -> access (Env.offset x xs)
  | Op (e0, op, e1) ->
    f8 e1 xs >> f8 e0 xs >> operation op
  | Fun (x, e) -> cur (f8t e (x :: xs))
  | App (e0, e2s) ->
    f8s e2s xs >> f8 e0 xs >> apply
  | Shift (x, e) -> shift (f8 e (x :: xs))
  | Control (x, e) -> control (f8 e (x :: xs))
  | Shift0 (x, e) -> shift0 (f8 e (x :: xs))
  | Control0 (x, e) -> control0 (f8 e (x :: xs))
  | Reset (e) -> reset (f8 e xs)

(* f8s : e list -> string list -> v list -> c -> s -> t -> m -> v list *)
and f8s e2s xs = match e2s with
    [] -> pushmark
  | e :: e2s -> f8s e2s xs >> f8 e xs

(* f8t : e -> string list -> v list -> c -> s -> t -> m -> v *)
and f8t e xs = match e with
    Num (n) -> num n >> return
  | Var (x) -> access (Env.offset x xs) >> return
  | Op (e0, op, e1) ->
    f8 e1 xs >> f8 e0 xs >> operation op >> return
  | Fun (x, e) ->
    grab (f8t e (x :: xs))
  | App (e0, e2s) ->
    f8s e2s xs >> f8 e0 xs >> apply >> return
  | Shift (x, e) -> shift (f8 e (x :: xs)) >> return
  | Control (x, e) -> control (f8 e (x :: xs)) >> return
  | Shift0 (x, e) -> shift0 (f8 e (x :: xs)) >> return
  | Control0 (x, e) -> control0 (f8 e (x :: xs)) >> return
  | Reset (e) -> reset (f8 e xs) >> return

(* f : e -> v *)
let f expr = f8 expr [] [] idc [] TNil MNil
