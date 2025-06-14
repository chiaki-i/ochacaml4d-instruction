open Syntax
open Value

(* Definitional interpreter for (λ-calculus with 4 delimited continuation operations : eval1s *)

(* initial continuation : v -> t -> m -> v *)
let idc v t m = match t with
    TNil ->
    begin match m with
        MNil -> v
      | MCons ((c, t), m) -> c v t m
    end
  | Trail (h) -> h v TNil m

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* f1: definitional interpreter *)

(* f1 : e -> string list -> v list -> c -> t -> m -> v *)
let rec f1 e xs vs c t m =
  match e with
    Num (n) -> c (VNum (n)) t m
  | Var (x) -> c (List.nth vs (Env.offset x xs)) t m
  | Op (e0, op, e1) ->
    f1 e1 xs vs (fun v1 t0 m0 ->
        f1 e0 xs vs (fun v0 t1 m1 ->
            begin match (v0, v1) with
                (VNum (n0), VNum (n1)) ->
                begin match op with
                    Plus -> c (VNum (n0 + n1)) t1 m1
                  | Minus -> c (VNum (n0 - n1)) t1 m1
                  | Times -> c (VNum (n0 * n1)) t1 m1
                  | Divide ->
                    if n1 = 0 then failwith "Division by zero"
                    else c (VNum (n0 / n1)) t1 m1
                end
              | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                               ^ " are not numbers")
            end) t0 m0) t m
  | Fun (x, e) ->
    c (VFun (fun v1 c' t' m' ->
              f1 e (x :: xs) (v1 :: vs) c' t' m')) t m
  | App (e0, e2s) ->
    f1s e2s xs vs (fun v2s t2 m2 ->
      f1 e0 xs vs (fun v0 t0 m0 ->
        apply1s v0 v2s c t0 m0) t2 m2) t m
  | Shift (x, e) -> f1 e (x :: xs) (VContS (c, t) :: vs) idc TNil m
  | Control (x, e) -> f1 e (x :: xs) (VContC (c, t) :: vs) idc TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) ->
          f1 e (x :: xs) (VContS (c, t) :: vs) c0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) ->
          f1 e (x :: xs) (VContC (c, t) :: vs) c0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f1 e xs vs idc TNil (MCons ((c, t), m))

(* f1s : e list -> string list -> v list -> c -> t -> m -> v list *)
and f1s e2s xs vs c t m = match e2s with
    [] -> c [] t m
  | e :: e2s ->
    f1s e2s xs vs (fun v2s t2 m2 ->
      f1 e xs vs (fun v1 t1 m1 ->
        c (v1 :: v2s) t1 m1) t2 m2) t m

(* apply1 : v -> v -> c -> t -> m -> v *)
and apply1 v0 v1 c t m = match v0 with
    VFun (f) -> f v1 c t m
  | VContS (c', t') -> c' v1 t' (MCons ((c, t), m))
  | VContC (c', t') -> c' v1 (apnd t' (cons c t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* apply1s : v -> v list -> c -> t -> m -> v *)
and apply1s v0 v2s c t m = match v2s with
    [] -> c v0 t m
  | v1 :: v2s -> apply1 v0 v1 (fun v t m ->
                   apply1s v v2s c t m) t m

(* f : e -> v *)
let f expr = f1 expr [] [] idc TNil MNil
