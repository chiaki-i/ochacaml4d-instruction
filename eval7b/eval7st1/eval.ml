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

(* mark on arg stack *)
let mark = VArgs ([])

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* f7: defunctionalized interpreter *)
(* f7: e -> string list -> v list -> c' -> s -> t -> m -> v *)
let rec f7 e xs vs c s t m = match e with
    Num (n) -> c (VNum (n) :: s) t m
  | Var (x) -> c ((List.nth vs (Env.offset x xs)) :: s) t m
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
      f7 e (x :: xs) (v1 :: vs) c' s' t' m')) :: s) t m
  | App (e0, e2s) ->
    f7s e2s xs vs (fun (VArgs (v2s) :: s) t m ->
      f7t e0 xs vs c (VArgs (v2s) :: s) t m) s t m
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

(* f7s : e list -> string list -> v list -> c -> s -> t -> m -> v list *)
and f7s e2s xs vs c s t m = match e2s with
    [] -> c (mark :: s) t m
  | e :: e2s ->
    f7s e2s xs vs (fun (VArgs (v2s) :: s) t m ->
      f7 e xs vs (fun (v :: VArgs (v2s) :: s) t m ->
        c (VArgs (v :: v2s) :: s) t m) (VArgs (v2s) :: s) t m
      ) s t m

(* f7t : e -> string list -> v list -> c -> s -> t -> m -> v *)
and f7t e xs vs c s t m = match s with VArgs (v2s) :: s ->
  let ret_c (v :: VArgs (v2s) :: s) t m = apply7s v v2s c s t m in
  let ret_s = VArgs (v2s) :: s in
  match e with
    Num (n) -> ret_c (VNum (n) :: ret_s) t m
  | Var (x) -> ret_c (List.nth vs (Env.offset x xs) :: ret_s) t m
  | Op (e0, op, e1) ->
    f7 e1 xs vs (fun (v :: s) t m ->
      f7 e0 xs vs (fun (v :: v0 :: s) t m ->
        begin match (v, v0) with
            (VNum (n0), VNum (n1)) ->
            begin match op with
                Plus -> ret_c (VNum (n0 + n1) :: s) t m
              | Minus -> ret_c (VNum (n0 - n1) :: s) t m
              | Times -> ret_c (VNum (n0 * n1) :: s) t m
              | Divide ->
                if n1 = 0 then failwith "Division by zero"
                else ret_c (VNum (n0 / n1) :: s) t m
            end
          | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
        end) (v :: s) t m) ret_s t m
  | Fun (x, e) ->
    begin match v2s with
      [] ->
      c ((VFun (fun c' (v1 :: s') t' m' ->
        f7 e (x :: xs) (v1 :: vs) c' s' t' m')) :: s) t m
    | v1 :: v2s -> f7t e (x :: xs) (v1 :: vs) c (VArgs (v2s) :: s) t m
    end
  | App (e0, e2s) ->
    f7s e2s xs vs (fun (VArgs (v2s) :: s) t m ->
      f7t e0 xs vs ret_c (VArgs (v2s) :: ret_s) t m) s t m
  | Shift (x, e) ->
    f7 e (x :: xs) (VContS (ret_c, ret_s, t) :: vs) idc [] TNil m
  | Control (x, e) ->
    f7 e (x :: xs) (VContC (ret_c, ret_s, t) :: vs) idc [] TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        f7 e (x :: xs) (VContS (ret_c, ret_s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        f7 e (x :: xs) (VContC (ret_c, ret_s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f7 e xs vs idc [] TNil (MCons ((ret_c, ret_s, t), m))

  (* apply7 : v -> v -> c -> s -> t -> m -> v *)
and apply7 v0 v1 c s t m = match v0 with
    VFun (f) -> f c (v1 :: s) t m
  | VContS (c', s', t') -> c' (v1 :: s') t' (MCons ((c, s, t), m))
  | VContC (c', s', t') ->
    c' (v1 :: s') (apnd t' (cons (fun v t m -> c (v :: s) t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* apply7s : v -> v list -> c -> s -> t -> m -> v *)
and apply7s v0 v2s c s t m = match v2s with
    [] -> c (v0 :: s) t m
  | v1 :: v2s ->
    apply7 v0 v1 (fun (v :: VArgs (v2s) :: s) t m ->
      apply7s v v2s c s t m) (VArgs (v2s) :: s) t m

(* f : e -> v *)
let f expr = f7 expr [] [] idc [] TNil MNil
