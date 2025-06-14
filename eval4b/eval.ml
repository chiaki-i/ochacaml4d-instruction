open Syntax
open Value

(* defunctionalized interpreter with argument stack: eval5st *)
(* v2s used to represent arguments of current closure, now integrated into s, delimited with VEmpty *)

(* initial continuation *)
let idc = C0

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* run_c5 : c -> v -> s -> t -> m -> v *)
let rec run_c5 c v s t m = match (c, s) with
    (C0, []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t), m) -> run_c5 c v s t m
        end
      | Trail (h) -> h v TNil m
    end
  | (COp1 (e0, xs, op, vs, c), s) ->
    f5 e0 xs vs (COp0 (op, c)) (v :: s) t m
  | (COp0 (op, c), v0 :: s) ->
    begin match (v, v0) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> run_c5 c (VNum (n0 + n1)) s t m
          | Minus -> run_c5 c (VNum (n0 - n1)) s t m
          | Times -> run_c5 c (VNum (n0 * n1)) s t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c5 c (VNum (n0 / n1)) s t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
    end
  | (CApp (c), s) -> apply5s v c s t m
  | (CApp1 (c), v1 :: s) -> apply5 v v1 c s t m
  | (CAppS0 (cs), s) -> run_c5s cs (v :: s) t m
  | _ -> failwith "run_c5: unexpected c"

(* run_c5s : cs -> v list -> s -> t -> m -> v *)
and run_c5s c s t m = match (c, s) with
    (CAppS1 (e, xs, vs, c), s) ->
    f5 e xs vs (CAppS0 (c)) s t m
  | (CAppS2 (e, xs, vs, c), s) ->
    begin match s with (v1 :: s) ->
        f5 e xs vs (CApp1 (c)) (v1 :: s) t m
      | _ -> failwith "run_c5s: unexpected v2s"
    end
  | _ -> failwith "run_c5s: unexpected c"

(* f5: defunctionalized interpreter *)
(* f5 : e -> string list -> v list -> c -> s -> t -> m -> v *)
and f5 e xs vs c s t m = match e with
    Num (n) -> run_c5 c (VNum (n)) s t m
  | Var (x) -> run_c5 c (List.nth vs (Env.offset x xs)) s t m
  | Op (e0, op, e1) -> f5 e1 xs vs (COp1 (e0, xs, op, vs, c)) s t m
  | Fun (x, e) ->
    run_c5 c (VFun (fun v1 c' s' t' m' ->
      f5t e (x :: xs) (v1 :: vs) c' s' t' m')) s t m
  | App (e0, e2s) ->
    f5s e2s xs vs (CAppS2 (e0, xs, vs, c)) s t m
  | Shift (x, e) -> f5 e (x :: xs) (VContS (c, s, t) :: vs) idc [] TNil m
  | Control (x, e) -> f5 e (x :: xs) (VContC (c, s, t) :: vs) idc [] TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        f5 e (x :: xs) (VContS (c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        f5 e (x :: xs) (VContC (c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f5 e xs vs idc [] TNil (MCons ((c, s, t), m))

(* f5s : e list -> string list -> v list -> cs -> s -> t -> m -> v list *)
and f5s e2s xs vs cs s t m = match e2s with
    [] -> run_c5s cs (VEmpty :: s) t m
  | e :: e2s ->
    f5s e2s xs vs (CAppS1 (e, xs, vs, cs)) s t m

(* f5t : e -> string list -> v list -> c -> s -> t -> m -> v *)
and f5t e xs vs c s t m =
  let app_c = CApp (c) in
  match e with
    Num (n) -> run_c5 app_c (VNum (n)) s t m
  | Var (x) -> run_c5 app_c (List.nth vs (Env.offset x xs)) s t m
  | Op (e0, op, e1) -> f5 e1 xs vs (COp1 (e0, xs, op, vs, app_c)) s t m
  | Fun (x, e) ->
    begin match s with
      VEmpty :: s ->
        run_c5 c (VFun (fun v1 c' s' t' m' ->
          f5t e (x :: xs) (v1 :: vs) c' s' t' m')) s t m
    | v1 :: s -> f5t e (x :: xs) (v1 :: vs) c s t m
    | _ -> failwith "apply5s: stack is empty"
    end
  | App (e0, e2s) ->
    f5s e2s xs vs (CAppS2 (e0, xs, vs, app_c)) s t m
  | Shift (x, e) ->
    f5 e (x :: xs) (VContS (app_c, s, t) :: vs) idc [] TNil m
  | Control (x, e) ->
    f5 e (x :: xs) (VContC (app_c, s, t) :: vs) idc [] TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        f5 e (x :: xs) (VContS (app_c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        f5 e (x :: xs) (VContC (app_c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f5 e xs vs idc [] TNil (MCons ((app_c, s, t), m))

(* apply5 : v -> v -> c -> s -> t -> m -> v *)
and apply5 v0 v1 c s t m =
  match v0 with
    VFun (f) -> f v1 c s t m
  | VContS (c', s', t') ->
    let app_c = CApp (c) in
    run_c5 c' v1 s' t' (MCons ((app_c, s, t), m))
  | VContC (c', s', t') ->
    let app_c = CApp (c) in
    run_c5 c' v1 s' (apnd t' (cons (fun v t m -> run_c5 app_c v s t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* apply5s : v -> v list -> c -> s -> t -> m -> v *)
and apply5s v0 c s t m = match s with
    VEmpty :: s -> run_c5 c v0 s t m
  | v1 :: s -> apply5 v0 v1 c s t m
  | _ -> failwith "apply5s: stack is empty"

(* f : e -> v *)
let f expr = f5 expr [] [] idc [] TNil MNil
