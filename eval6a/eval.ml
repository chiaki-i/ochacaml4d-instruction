open Syntax
open Value

(* interpreter with *re*-funtionalized continuations, *)
(* and arg stack with value on top of it: eval7st1 *)

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
  | _ -> failwith "idc: stack error"

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* f7: defunctionalized interpreter *)
(* f7: e -> string list -> v list -> c -> s -> t -> m -> v *)
let rec f7 e xs vs c s t m = match e with
    Num (n) -> c (VNum (n) :: s) t m
  | Var (x) -> c (List.nth vs (Env.offset x xs) :: s) t m
  | Op (e0, op, e1) ->
    f7 e1 xs vs (fun (v :: s) t m ->
      f7 e0 xs vs (fun (v :: v0 :: s) t m ->
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
        end) (v :: s) t m) s t m
  | Fun (x, e) ->
    c ((VFun (fun c' (v1 :: s') t' m' ->
      f7t e (x :: xs) (v1 :: vs) c' s' t' m')) :: s) t m
  | App (e0, e2s) ->
    f7s e2s xs vs (fun (v1 :: s) t m ->
      f7 e0 xs vs (fun (v :: v1 :: s) t m ->
        apply7 v v1 c s t m) (v1 :: s) t m) s t m
  | Shift (x, e) -> f7 e (x :: xs) (VContS (c, s, t) :: vs) idc [] TNil m
  | Control (x, e) -> f7 e (x :: xs) (VContC (c, s, t) :: vs) idc [] TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        f7 e (x :: xs) (VContS (c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        f7 e (x :: xs) (VContC (c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f7 e xs vs idc [] TNil (MCons ((c, s, t), m))

(* f7s : e list -> string list -> v list -> cs -> s -> t -> m -> v list *)
and f7s e2s xs vs c s t m = match e2s with
    [] -> c (VEmpty :: s) t m
  | e :: e2s ->
    f7s e2s xs vs (fun s t m ->
      f7 e xs vs (fun (v :: s) t m ->
        c (v :: s) t m) s t m
      ) s t m

(* f7t : e -> string list -> v list -> c -> s -> t -> m -> v *)
and f7t e xs vs c s t m =
  let app_c = fun (v :: s) t m -> apply7s v c s t m in
  match e with
    Num (n) -> app_c (VNum (n) :: s) t m
  | Var (x) -> app_c (List.nth vs (Env.offset x xs) :: s) t m
  | Op (e0, op, e1) ->
    f7 e1 xs vs (fun (v :: s) t m ->
      f7 e0 xs vs (fun (v :: v0 :: s) t m ->
        begin match (v, v0) with
            (VNum (n0), VNum (n1)) ->
            begin match op with
                Plus -> app_c (VNum (n0 + n1) :: s) t m
              | Minus -> app_c (VNum (n0 - n1) :: s) t m
              | Times -> app_c (VNum (n0 * n1) :: s) t m
              | Divide ->
                if n1 = 0 then failwith "Division by zero"
                else app_c (VNum (n0 / n1) :: s) t m
            end
          | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
        end) (v :: s) t m) s t m
  | Fun (x, e) ->
    begin match s with
        VEmpty :: s ->
        c ((VFun (fun c' (v1 :: s') t' m' ->
          f7t e (x :: xs) (v1 :: vs) c' s' t' m')) :: s) t m
      | v1 :: s -> f7t e (x :: xs) (v1 :: vs) c s t m
      | _ -> failwith "f7t: Fun: stack is empty"
    end
  | App (e0, e2s) ->
    f7s e2s xs vs (fun s t m ->
      begin match s with v1 :: s ->
        f7 e0 xs vs (fun (v0 :: v1 :: s) t m ->
          apply7 v0 v1 app_c s t m) (v1 :: s) t m
      | _ -> failwith "run_c7s: unexpected s"
      end) s t m
  | Shift (x, e) ->
    f7 e (x :: xs) (VContS (app_c, s, t) :: vs) idc [] TNil m
  | Control (x, e) ->
    f7 e (x :: xs) (VContC (app_c, s, t) :: vs) idc [] TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        f7 e (x :: xs) (VContS (app_c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        f7 e (x :: xs) (VContC (app_c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f7 e xs vs idc [] TNil (MCons ((app_c, s, t), m))

(* apply7 : v -> v -> c -> s -> t -> m -> v *)
and apply7 v0 v1 c s t m =
  let app_c = fun (v :: s) t m -> apply7s v c s t m in
  match v0 with
    VFun (f) -> f c (v1 :: s) t m
  | VContS (c', s', t') -> c' (v1 :: s') t' (MCons ((app_c, s, t), m))
  | VContC (c', s', t') ->
    c' (v1 :: s') (apnd t' (cons (fun v t m -> app_c (v :: s) t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* apply7s : v -> v list -> c -> s -> t -> m -> v *)
(* return and apply *)
and apply7s v0 c s t m = match s with
    VEmpty :: s -> c (v0 :: s) t m
  | v1 :: s -> apply7 v0 v1 c s t m

(* f : e -> v *)
let f expr = f7 expr [] [] idc [] TNil MNil
