open Syntax
open Value

(* linearize eval9st1: eval10st *)

(* initial continuation *)
let idc = []

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

let rec run_c10 c s t m = match (c, s) with
    ([], v :: []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t), m) -> run_c10 c (v :: s) t m
        end
      | Trail (h) -> h v TNil m
    end
  | ((([], vs) :: c), s) -> run_c10 c s t m
  (* is = instructions, vs = env, c = ret stack *)
  | ((INum (n) :: is, vs) :: c, s) ->
    run_c10 ((is, vs) :: c) (VNum (n) :: s) t m
  | ((IAccess (n) :: is, vs) :: c, s) ->
    run_c10 ((is, vs) :: c) (List.nth vs n :: s) t m
  | ((IOp (op) :: is, vs) :: c, s) ->
    begin match s with v :: v0 :: s ->
        begin match (v, v0) with
            (VNum (n0), VNum (n1)) ->
            begin match op with
                Plus -> run_c10 ((is, vs) :: c) (VNum (n0 + n1) :: s) t m
              | Minus -> run_c10 ((is, vs) :: c) (VNum (n0 - n1) :: s) t m
              | Times -> run_c10 ((is, vs) :: c) (VNum (n0 * n1) :: s) t m
              | Divide ->
                if n1 = 0 then failwith "Division by zero"
                else run_c10 ((is, vs) :: c) (VNum (n0 / n1) :: s) t m
            end
          | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
        end
      | _ -> failwith "IOp: unexpected s"
    end
  | ((ICur (is') :: is, vs) :: c, s) ->
    run_c10 ((is, vs) :: c) (VFun (is', vs) :: s) t m
  | ((IGrab (is') :: [], vs) :: c, s) ->
    begin match s with
        VEmpty :: s ->
        run_c10 c (VFun (is', vs) :: s) t m
      | v1 :: s ->
        run_c10 ((is', (v1 :: vs)) :: c) s t m
      | _ -> failwith "IGrab: unexpected s"
    end
  | ((IApply :: is, vs) :: c, s) ->
    begin match s with (v :: v1 :: s) ->
        apply10 v v1 vs ((is, vs) :: c) s t m
      | _ -> failwith "IApply: unexpected s"
    end
  | ((IReturn :: [], vs) :: c, s) ->
    begin match s with (v :: s) ->
        apply10s v vs c s t m
      | _ -> failwith "IReturn: unexpected s"
    end
  | ((IPushmark :: is, vs) :: c, s) ->
    run_c10 ((is, vs) :: c) (VEmpty :: s) t m
  | ((IShift (i) :: is, vs) :: c, s) ->
    run_c10
      ((i, VContS (((is, vs) :: c), s, t) :: vs) :: idc)
      [] TNil m
  | ((IControl (i) :: is, vs) :: c, s) ->
    run_c10
      ((i, VContC (((is, vs) :: c), s, t) :: vs) :: idc)
      [] TNil m
  | ((IShift0 (i) :: is, vs) :: c, s) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        run_c10
          ((i, VContS (((is, vs) :: c), s, t) :: vs) :: c0)
          s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | ((IControl0 (i) :: is, vs) :: c, s) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        run_c10
          ((i, VContC (((is, vs) :: c), s, t) :: vs) :: c0)
          s0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | ((IReset (i) :: is, vs) :: c, s) ->
    run_c10
      ((i, vs) :: idc)
      [] TNil (MCons ((((is, vs) :: c), s, t), m))
  | _ -> failwith "run_c10: stack error"

(* apply10 : v -> v -> v list -> c -> s -> t -> m -> v *)
and apply10 v0 v1 vs c s t m =
  match v0 with
    VFun (is, vs') -> run_c10 ((is, (v1 :: vs')) :: c) s t m
  | VContS (c', s', t') ->
    let app_c = ([IReturn], vs) :: c in
    run_c10 c' (v1 :: s') t' (MCons ((app_c, s, t), m))
  | VContC (c', s', t') ->
    let app_c = ([IReturn], vs) :: c in
    run_c10 c' (v1 :: s') (apnd t' (cons (fun v t m -> run_c10 app_c (v :: s) t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* apply10s : v -> v list -> c -> s -> t -> m -> v *)
and apply10s v0 vs c s t m = match s with
    VEmpty :: s -> run_c10 c (v0 :: s) t m
  | v1 :: s -> apply10 v0 v1 vs c s t m

(* f10: e -> string list -> i list *)
let rec f10 e xs = match e with
    Num (n) -> [INum (n)]
  | Var (x) -> [IAccess (Env.offset x xs)]
  | Op (e0, op, e1) ->
    f10 e1 xs @ f10 e0 xs @ [IOp (op)]
  | Fun (x, e) -> [ICur (f10t e (x :: xs))]
  | App (e0, e2s) ->
    f10s e2s xs @ f10 e0 xs @ [IApply]
  | Shift (x, e) -> [IShift (f10 e (x :: xs))]
  | Control (x, e) -> [IControl (f10 e (x :: xs))]
  | Shift0 (x, e) -> [IShift0 (f10 e (x :: xs))]
  | Control0 (x, e) -> [IControl0 (f10 e (x :: xs))]
  | Reset (e) -> [IReset (f10 e xs)]

(* f10s : e list -> string list -> i list *)
and f10s e2s xs = match e2s with
    [] -> [IPushmark]
  | e :: e2s -> f10s e2s xs @ f10 e xs

(* f10t : e -> string list -> i list *)
and f10t e xs = match e with
    Num (n) -> [INum n; IReturn]
  | Var (x) -> [IAccess (Env.offset x xs); IReturn]
  | Op (e0, op, e1) ->
    f10 e1 xs @ f10 e0 xs @ [IOp (op); IReturn]
  | Fun (x, e) -> [IGrab (f10t e (x :: xs))]
  | App (e0, e2s) -> f10s e2s xs @ f10 e0 xs @ [IApply; IReturn]
  | Shift (x, e) -> [IShift (f10 e (x :: xs)); IReturn]
  | Control (x, e) -> [IControl (f10 e (x :: xs)); IReturn]
  | Shift0 (x, e) -> [IShift0 (f10 e (x :: xs)); IReturn]
  | Control0 (x, e) -> [IControl0 (f10 e (x :: xs)); IReturn]
  | Reset (e) -> [IReset (f10 e xs); IReturn]

(* f : e -> v *)
let f expr = run_c10 ((f10 expr [], []) :: []) [] TNil MNil
