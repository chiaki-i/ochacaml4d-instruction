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

(* run_c : c -> v -> t -> m -> v *)
let rec run_c c v t m = match c with
    C0 -> begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, t), m) -> run_c c v t m
        end
      | Trail (h) -> h v TNil m
    end
  | COp1 (e, xs, op, vs, c) -> f e xs vs (COp0 (v, op, c)) t m
  | COp0 (v0, op, c) ->
    begin match (v, v0) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> run_c c (VNum (n0 + n1)) t m
          | Minus -> run_c c (VNum (n0 - n1)) t m
          | Times -> run_c c (VNum (n0 * n1)) t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c c (VNum (n0 / n1)) t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
    end
  | CApp1 (v1 :: v2s, c) -> app v v1 v2s c t m
  | CApp2 (v2s, c) -> run_cs c (v :: v2s) t m
  | CApp3 (v2s, c) -> app_s v v2s c t m

(* run_cs : c -> v -> t -> m -> v *)
and run_cs c v2s t m = match c with
    CAppS1 (e, xs, vs, c) -> f e xs vs (CApp1 (v2s, c)) t m
  | CAppS2 (e, xs, vs, c) -> f e xs vs (CApp2 (v2s, c)) t m

(* f : definitional interpreter *)
(* f : e -> string list -> v list -> c -> t -> m -> v *)
and f e xs vs c t m =
  match e with
    Num (n) -> run_c c (VNum (n)) t m
  | Var (x) -> run_c c (List.nth vs (Env.off_set x xs)) t m
  | Op (e0, op, e1) -> f e1 xs vs (COp1 (e0, xs, op, vs, c)) t m
  | Fun (x, e) ->
    run_c c (VFun (fun v1 v2s' c' t' m' ->
              f_t e (x :: xs) (v1 :: vs) v2s' c' t' m')) t m
  | App (e0, e2s) ->
    f_s e2s xs vs (CAppS1 (e0, xs, vs, c)) t m
  | Shift (x, e) -> f e (x :: xs) (VContS (c, t) :: vs) idc TNil m
  | Control (x, e) -> f e (x :: xs) (VContC (c, t) :: vs) idc TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) ->
          f e (x :: xs) (VContS (c, t) :: vs) c0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) ->
          f e (x :: xs) (VContC (c, t) :: vs) c0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f e xs vs idc TNil (MCons ((c, t), m))

(* f_t : e -> string list -> v list -> v list -> c -> t -> m -> v *)
and f_t e xs vs v2s' c t m =
  let app_c = CApp3 (v2s', c) in
  match e with
    Num (n) -> run_c app_c (VNum (n)) t m
  | Var (x) -> run_c app_c (List.nth vs (Env.off_set x xs)) t m
  | Op (e0, op, e1) -> f e1 xs vs (COp1 (e0, xs, op, vs, app_c)) t m
  | Fun (x, e) ->
    begin match v2s' with
        [] -> run_c c (VFun (fun v1 v2s' c' t' m' ->
          f_t e (x :: xs) (v1 :: vs) v2s' c' t' m')) t m
      | v1 :: v2s' -> f_t e (x :: xs) (v1 :: vs) v2s' c t m
    end
    (* run_c app_c (VFun (fun v1 v2s' c' t' m' ->
              f_t e (x :: xs) (v1 :: vs) v2s' c' t' m')) t m *)
  | App (e0, e2s) ->
    f_st e2s xs vs v2s' (CAppS1 (e0, xs, vs, c)) t m
  | Shift (x, e) -> f e (x :: xs) (VContS (app_c, t) :: vs) idc TNil m
  | Control (x, e) -> f e (x :: xs) (VContC (app_c, t) :: vs) idc TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) ->
          f e (x :: xs) (VContS (app_c, t) :: vs) c0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) ->
          f e (x :: xs) (VContC (app_c, t) :: vs) c0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f e xs vs idc TNil (MCons ((app_c, t), m))

(* f_s : e list -> string list -> v list -> c -> t -> m -> v list *)
and f_s e2s xs vs c t m = match e2s with
    [] -> run_cs c [] t m
  | e :: e2s ->
    f_s e2s xs vs (CAppS2 (e, xs, vs, c)) t m

(* f_st : e list -> string list -> v list -> v list -> c -> t -> m -> v list *)
and f_st e2s xs vs v2s' c t m = match e2s with
    [] -> run_cs c v2s' t m
  | e :: e2s ->
    f_st e2s xs vs v2s' (CAppS2 (e, xs, vs, c)) t m

(* app : v -> v -> v list -> c -> t -> m -> v *)
and app v0 v1 v2s' c t m =
  let app_c = CApp3 (v2s', c) in
  match v0 with
    VFun (f) -> f v1 v2s' c t m
  | VContS (c', t') -> run_c c' v1 t' (MCons ((app_c, t), m))
  | VContC (c', t') -> run_c c' v1 (apnd t' (cons (fun v t m -> app_s v v2s' c t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* app_s : v -> v list -> c -> t -> m -> v *)
and app_s v0 v2s c t m = match v2s with
    [] -> run_c c v0 t m
  | v1 :: v2s -> app v0 v1 v2s c t m

(* f_init : e -> v *)
let f_init expr = f expr [] [] idc TNil MNil
