open Syntax
open Value

(* Definitional interpreter for (λ-calculus with 4 delimited continuation operations : eval1s *)

(* initial continuation : v -> t -> m -> v *)
let idc = C0

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* run_c : c -> v -> s -> t -> m -> v *)
let rec run_c c v s t m = match (c, s) with
    (C0, []) -> begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t), m) -> run_c c v s t m
        end
      | Trail (h) -> h v TNil m
    end
  | (COp1 (e, xs, op, vs, c), s) -> f e xs vs (COp0 (v, op, c)) s t m
  | (COp0 (v0, op, c), s) ->
    begin match (v, v0) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> run_c c (VNum (n0 + n1)) s t m
          | Minus -> run_c c (VNum (n0 - n1)) s t m
          | Times -> run_c c (VNum (n0 * n1)) s t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c c (VNum (n0 / n1)) s t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
    end
  | (CApp1 (c), v1 :: s) -> app v v1 c s t m
  | (CApp2 (c), s) -> run_cs c (v :: s) t m
  | (CApp3 (c), s) -> app_s v c s t m

(* run_cs : c -> v -> s -> t -> m -> v *)
and run_cs c s t m = match (c, s) with
    (CAppS1 (e, xs, vs, c), s) -> f e xs vs (CApp1 (c)) s t m
  | (CAppS2 (e, xs, vs, c), s) -> f e xs vs (CApp2 (c)) s t m

(* f : definitional interpreter *)
(* f : e -> string list -> v list -> c -> s -> t -> m -> v *)
and f e xs vs c s t m =
  match e with
    Num (n) -> run_c c (VNum (n)) s t m
  | Var (x) -> run_c c (List.nth vs (Env.off_set x xs)) s t m
  | Op (e0, op, e1) -> f e1 xs vs (COp1 (e0, xs, op, vs, c)) s t m
  | Fun (x, e) ->
    run_c c (VFun (fun v1 c' s' t' m' ->
      f_t e (x :: xs) (v1 :: vs) c' s' t' m')) s t m
  | App (e0, e2s) ->
    f_s e2s xs vs (CAppS1 (e0, xs, vs, c)) s t m
  | Shift (x, e) -> f e (x :: xs) (VContS (c, s, t) :: vs) idc [] TNil m
  | Control (x, e) -> f e (x :: xs) (VContC (c, s, t) :: vs) idc [] TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
          f e (x :: xs) (VContS (c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
          f e (x :: xs) (VContC (c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f e xs vs idc [] TNil (MCons ((c, s, t), m))

(* f_t : e -> string list -> v list -> v list -> c -> s -> t -> m -> v *)
and f_t e xs vs c s t m =
  let app_c = CApp3 (c) in
  match e with
    Num (n) -> run_c app_c (VNum (n)) s t m
  | Var (x) -> run_c app_c (List.nth vs (Env.off_set x xs)) s t m
  | Op (e0, op, e1) -> f e1 xs vs (COp1 (e0, xs, op, vs, app_c)) s t m
  | Fun (x, e) ->
    begin match s with
        VEmpty :: s -> run_c c (VFun (fun v1 c' s' t' m' ->
          f_t e (x :: xs) (v1 :: vs) c' s' t' m')) s t m
      | v1 :: s -> f_t e (x :: xs) (v1 :: vs) c s t m
    end
    (* run_c app_c (VFun (fun v1 c' s' t' m' ->
      f_t e (x :: xs) (v1 :: vs) c' s' t' m')) s t m *)
  | App (e0, e2s) ->
    f_st e2s xs vs (CAppS1 (e0, xs, vs, c)) s t m
  | Shift (x, e) -> f e (x :: xs) (VContS (app_c, s, t) :: vs) idc [] TNil m
  | Control (x, e) -> f e (x :: xs) (VContC (app_c, s, t) :: vs) idc [] TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
          f e (x :: xs) (VContS (app_c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
          f e (x :: xs) (VContC (app_c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f e xs vs idc [] TNil (MCons ((app_c, s, t), m))

(* f_s : e list -> string list -> c -> s -> t -> m -> v list *)
and f_s e2s xs vs c s t m = match e2s with
    [] -> run_cs c (VEmpty :: s) t m
  | e :: e2s ->
    f_s e2s xs vs (CAppS2 (e, xs, vs, c)) s t m

(* f_st : e list -> string list -> v list -> c -> s -> t -> m -> v list *)
and f_st e2s xs vs c s t m = match e2s with
    [] -> run_cs c s t m
  | e :: e2s ->
    f_st e2s xs vs (CAppS2 (e, xs, vs, c)) s t m

(* app : v -> v -> c -> s -> t -> m -> v *)
and app v0 v1 c s t m =
  let app_c = CApp3 (c) in
  match v0 with
    VFun (f) -> f v1 c s t m
  | VContS (c', s', t') -> run_c c' v1 s' t' (MCons ((app_c, s, t), m))
  | VContC (c', s', t') -> run_c c' v1 s' (apnd t' (cons (fun v t m -> app_s v c s t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* app_s : v -> v list -> c -> s -> t -> m -> v *)
and app_s v0 c s t m = match s with
    VEmpty :: s -> run_c c v0 s t m
  | v1 :: s -> app v0 v1 c s t m
  | [] -> failwith "unexpected s"

(* f_init : e -> v *)
let f_init expr = f expr [] [] idc [] TNil MNil
