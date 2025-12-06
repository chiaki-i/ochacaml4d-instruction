open Syntax
open Value

(* Definitional interpreter for (λ-calculus with 4 delimited continuation operations : eval1s *)

(* initial continuation : v -> t -> m -> v *)
let idc s t m = match s with
    v :: [] ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t), m) -> c (v :: s) t m
        end
      | Trail (h) -> h v TNil m
    end
  | _ -> failwith "idc: stack error"

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

(* cur : i -> i *)
let cur i = fun vs c s t m ->
  c ((VFun (fun c' (v1 :: s') t' m' ->
    i (v1 :: vs) c' s' t' m')) :: s) t m

(* grab: i -> i *)
let grab i = fun vs c s t m ->
  begin match s with
    VEmpty :: s ->
    c ((VFun (fun c' (v1 :: s') t' m' ->
      i (v1 :: vs) c' s' t' m')) :: s) t m
  | v1 :: s -> i (v1 :: vs) c s t m
  | _ -> failwith "grab: stack is empty"
  end

(* app : v -> v -> c -> s -> t -> m -> v *)
let rec app v0 v1 c s t m =
  let app_c (v :: s) t m = app_s v c s t m in
  match v0 with
    VFun (f) -> f c (v1 :: s) t m
  | VContS (c', s', t') ->
    c' (v1 :: s') t' (MCons ((app_c, s, t), m))
  | VContC (c', s', t') ->
    c' (v1 :: s') (apnd t' (cons (fun v t m -> app_s v c s t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* app_s : v -> v list -> c -> s -> t -> m -> v *)
and app_s v0 c s t m = match s with
    VEmpty :: s -> c (v0 :: s) t m
  | v1 :: s -> app v0 v1 c s t m
  | [] -> failwith "unexpected s"

(* apply : i *)
let apply = fun vs c (v :: v1 :: s) t m ->
  app v v1 c s t m

(* pushmark : i *)
let pushmark = fun vs c s t m -> c (VEmpty :: s) t m

(* skip : i *)
let skip = fun vs c s t m -> c s t m

(* return : i *)
let return = fun vs c (v :: s) t m ->
  app_s v c s t m

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

(* f : definitional interpreter *)
(* f : e -> string list -> v list -> c -> s -> t -> m -> v *)
let rec f e xs = match e with
    Num (n) -> num n
  | Var (x) -> access (Env.off_set x xs)
  | Op (e0, op, e1) ->
    f e1 xs >> f e0 xs >> operation op
  | Fun (x, e) -> cur (f_t e (x :: xs))
  | App (e0, e2s) ->
    f_s e2s xs >> f e0 xs >> apply
  | Shift (x, e) -> shift (f e (x :: xs))
  | Control (x, e) -> control (f e (x :: xs))
  | Shift0 (x, e) -> shift0 (f e (x :: xs))
  | Control0 (x, e) -> control0 (f e (x :: xs))
  | Reset (e) -> reset (f e xs)

(* f_t : e -> string list -> v list -> v list -> c -> s -> t -> m -> v *)
and f_t e xs = match e with
    Num (n) -> num n >> return
  | Var (x) -> access (Env.off_set x xs) >> return
  | Op (e0, op, e1) ->
    f e1 xs >> f e0 xs >> operation op >> return
  | Fun (x, e) -> grab (f_t e (x :: xs))
  | App (e0, e2s) ->
    f_st e2s xs >> f e0 xs >> apply
  | Shift (x, e) -> shift (f e (x :: xs)) >> return
  | Control (x, e) -> control (f e (x :: xs)) >> return
  | Shift0 (x, e) -> shift0 (f e (x :: xs)) >> return
  | Control0 (x, e) -> control0 (f e (x :: xs)) >> return
  | Reset (e) -> reset (f e xs) >> return

(* f_s : e list -> string list -> i *)
and f_s e2s xs = match e2s with
    [] -> pushmark
  | e :: e2s -> f_s e2s xs >> f e xs

(* f_st : e list -> string list -> i *)
and f_st e2s xs = match e2s with
    [] -> skip
  | e :: e2s -> f_st e2s xs >> f e xs

(* f_init : e -> v *)
let f_init expr = f expr [] [] idc [] TNil MNil
