open Syntax
open Value

(* linearize eval9st1: eval10st *)

(* initial continuation *)
let idc = []

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

(* run_c10: c -> s -> t -> m -> v *)
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
          | _ -> failwith (to_string v0 ^ " or " ^ to_string v
                           ^ " are not numbers")
        end
      | _ -> failwith "IOp: unexpected s"
    end
  | ((ICur (i) :: is, vs) :: c, s) ->
    run_c10 ((is, vs) :: c) ((VFun (i, vs)) :: s) t m
  | ((IGrab (i) :: is, vs) :: c, s) ->
    begin match s with (VArgs (v2s) :: s) ->
        begin match v2s with
          [] -> run_c10 ((is, vs) :: c) ((VFun (i, vs)) :: s) t m
        | v1 :: v2s ->
          run_c10
            (((i, (v1 :: vs)) :: (IApply :: is, vs) :: c))
            (VArgs (v2s) :: s) t m
        end
      | _ -> failwith "IGrab: unexpected s"
    end
  | ((IApply :: is, vs) :: c, s) ->
    begin match s with (v :: VArgs (v2s) :: s) ->
        apply10s v v2s vs ((is, vs) :: c) s t m
      | _ -> failwith "IApply: unexpected s"
    end
  | ((IAppterm (i) :: is, vs) :: c, s) ->
    run_c10 ((i @ [IApply], vs) :: c) s t m
  | ((IPushmark :: is, vs) :: c, s) ->
    run_c10 ((is, vs) :: c) (mark :: s) t m
  | ((IPush :: is, vs) :: c, s) ->
    begin match s with v :: VArgs (v2s) :: s ->
        run_c10 ((is, vs) :: c) (VArgs (v :: v2s) :: s) t m
      | _ -> failwith "IPush: unexpected s"
    end
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

(* apply10 : v -> v -> c -> s -> t -> m -> v *)
and apply10 v0 v1 c s t m = match v0 with
    VFun (i, vs) ->
    run_c10 ((i, (v1 :: vs)) :: c) s t m
  | VContS (c', s', t') -> run_c10 c' (v1 :: s') t' (MCons ((c, s, t), m))
  | VContC (c', s', t') ->
    run_c10 c' (v1 :: s') (apnd t' (cons (fun v t m -> run_c10 c (v :: s) t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* apply10s : v -> v list -> c -> s -> t -> m -> v *)
and apply10s v0 v2s vs c s t m = match v2s with
    [] -> run_c10 c (v0 :: s) t m
  | v1 :: v2s ->
    apply10 v0 v1 (([IApply], vs) :: c) (VArgs (v2s) :: s) t m

(* f10: e -> string list -> i *)
let rec f10 e xs = match e with
    Num (n) -> [INum (n)]
  | Var (x) -> [IAccess (Env.offset x xs)]
  | Op (e0, op, e1) ->
    f10 e1 xs @ f10 e0 xs @ [IOp (op)]
  | Fun (x, e) -> [ICur (f10 e (x :: xs))]
  | App (e0, e2s) ->
    f10s e2s xs @ f10t e0 xs
  | Shift (x, e) -> [IShift (f10 e (x :: xs))]
  | Control (x, e) -> [IControl (f10 e (x :: xs))]
  | Shift0 (x, e) -> [IShift0 (f10 e (x :: xs))]
  | Control0 (x, e) -> [IControl0 (f10 e (x :: xs))]
  | Reset (e) -> [IReset (f10 e xs)]

(* f10s : e list -> string list -> v list -> c -> s -> t -> m -> v list *)
and f10s e2s xs = match e2s with
    [] -> [IPushmark]
  | e :: e2s -> f10s e2s xs @ f10 e xs @ [IPush]

(* f10t : e -> string list -> v list -> c -> s -> t -> m -> v *)
and f10t e xs = match e with
    Num (n) -> [INum n] @ [IApply]
  | Var (x) -> [IAccess (Env.offset x xs)] @ [IApply]
  | Op (e0, op, e1) ->
    f10 e1 xs @ f10 e0 xs @ [IOp (op)] @ [IApply]
  | Fun (x, e) -> [IGrab (f10 e (x :: xs))]
  | App (e0, e2s) -> f10s e2s xs @ [IAppterm (f10t e0 xs)]
  | Shift (x, e) -> [IShift (f10 e (x :: xs))] @ [IApply]
  | Control (x, e) -> [IControl (f10 e (x :: xs))] @ [IApply]
  | Shift0 (x, e) -> [IShift0 (f10 e (x :: xs))] @ [IApply]
  | Control0 (x, e) -> [IControl0 (f10 e (x :: xs))] @ [IApply]
  | Reset (e) -> [IReset (f10 e xs)] @ [IApply]

  (* f : e -> v *)
let f expr = run_c10 ((f10 expr [], []) :: []) [] TNil MNil
