open Syntax
open Value

(* Definitional interpreter for (λ-calculus with 4 delimited continuation operations : eval1s *)

(* initial continuation : c *)
let idc = []

(* cons : h -> t -> t *)
let cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (Append (h, h'))

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* run_h : h -> v -> t -> m -> v *)
let rec run_h h v t m = match h with
    Hold (c, s) -> run_c c (v :: s) t m
  | Append (h, h') -> run_h h v (cons h' t) m

(* run_c : c -> s -> t -> m -> v *)
and run_c c s t m = match (c, s) with
    ([], v :: []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t), m) -> run_c c (v :: s) t m
        end
      | Trail (h) -> run_h h v TNil m
    end
  | ((([], vs) :: c), s) -> run_c c s t m
  (* is = instructions, vs = env, c = ret stack *)
  | ((INum (n) :: is, vs) :: c, s) ->
    run_c ((is, vs) :: c) (VNum (n) :: s) t m
  | ((IAccess (n) :: is, vs) :: c, s) ->
    run_c ((is, vs) :: c) (List.nth vs n :: s) t m
  | ((IOp (op) :: is, vs) :: c, s) ->
    begin match s with v :: v0 :: s ->
        begin match (v, v0) with
            (VNum (n0), VNum (n1)) ->
            begin match op with
                Plus -> run_c ((is, vs) :: c) (VNum (n0 + n1) :: s) t m
              | Minus -> run_c ((is, vs) :: c) (VNum (n0 - n1) :: s) t m
              | Times -> run_c ((is, vs) :: c) (VNum (n0 * n1) :: s) t m
              | Divide ->
                if n1 = 0 then failwith "Division by zero"
                else run_c ((is, vs) :: c) (VNum (n0 / n1) :: s) t m
            end
          | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
        end
      | _ -> failwith "IOp: unexpected s"
    end
  | ((ICur (is') :: is, vs) :: c, s) ->
    run_c ((is, vs) :: c) (VFun (is', vs) :: s) t m
  | ((IGrab (is') :: is, vs) :: c, s) ->
    begin match s with
        VEmpty :: s ->
        run_c ((is, vs) :: c) (VFun (is', vs) :: s) t m
      | v1 :: s ->
        run_c ((is', (v1 :: vs)) :: (is, vs) :: c) s t m
      | _ -> failwith "IGrab: unexpected s"
    end
  | ((IApply :: is, vs) :: c, s) ->
    begin match s with
        VFun (is', vs') :: v1 :: s ->
        run_c ((is', (v1 :: vs')) :: (is, vs) :: c) s t m
      | VContS (c', s', t') :: v1 :: s ->
        let app_c = ([IReturn], vs) :: (is, vs) :: c in
        run_c c' (v1 :: s') t' (MCons ((app_c, s, t), m))
      | VContC (c', s', t') :: v1 :: s ->
        let app_c = ([IReturn], vs) :: (is, vs) :: c in
        run_c c' (v1 :: s') (apnd t' (cons (Hold (app_c, s)) t)) m
      | v0 :: v1 :: s ->
        failwith (to_string v0
          ^ " is not a function; it can not be applied.")
      | _ -> failwith "IApply: unexpected s"
    end
  | ((IReturn :: is, vs) :: c, s) ->
    begin match s with
        v :: VEmpty :: s -> run_c ((is, vs) :: c) (v :: s) t m
      | VFun (is', vs') :: v1 :: s ->
        run_c ((is', (v1 :: vs')) :: (is, vs) :: c) s t m
      | VContS (c', s', t') :: v1 :: s ->
        let app_c = ([IReturn], vs) :: (is, vs) :: c in
        run_c c' (v1 :: s') t' (MCons ((app_c, s, t), m))
      | VContC (c', s', t') :: v1 :: s ->
        let app_c = ([IReturn], vs) :: (is, vs) :: c in
        run_c c' (v1 :: s') (apnd t' (cons (Hold (app_c, s)) t)) m
      | v0 :: v1 :: s ->
        failwith (to_string v0
          ^ " is not a function; it can not be applied.")
      | _ -> failwith "IReturn: unexpected s"
    end
  | ((IPushmark :: is, vs) :: c, s) ->
    run_c ((is, vs) :: c) (VEmpty :: s) t m
  | ((IShift (i) :: is, vs) :: c, s) ->
    run_c
      ((i, VContS (((is, vs) :: c), s, t) :: vs) :: idc)
      [] TNil m
  | ((IControl (i) :: is, vs) :: c, s) ->
    run_c
      ((i, VContC (((is, vs) :: c), s, t) :: vs) :: idc)
      [] TNil m
  | ((IShift0 (i) :: is, vs) :: c, s) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        run_c
          ((i, VContS (((is, vs) :: c), s, t) :: vs) :: c0)
          s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | ((IControl0 (i) :: is, vs) :: c, s) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        run_c
          ((i, VContC (((is, vs) :: c), s, t) :: vs) :: c0)
          s0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | ((IReset (i) :: is, vs) :: c, s) ->
    run_c
      ((i, vs) :: idc)
      [] TNil (MCons ((((is, vs) :: c), s, t), m))
  | _ -> failwith "run_c: stack error"

(* f : definitional interpreter *)
(* f : e -> string list -> i *)
let rec f e xs = match e with
    Num (n) -> [INum (n)]
  | Var (x) -> [IAccess (Env.off_set x xs)]
  | Op (e0, op, e1) ->
    f e1 xs @ f e0 xs @ [IOp (op)]
  | Fun (x, e) -> [ICur (f_t e (x :: xs))]
  | App (e0, e2s) ->
    f_s e2s xs @ f e0 xs @ [IApply]
  | Shift (x, e) -> [IShift (f e (x :: xs))]
  | Control (x, e) -> [IControl (f e (x :: xs))]
  | Shift0 (x, e) -> [IShift0 (f e (x :: xs))]
  | Control0 (x, e) -> [IControl0 (f e (x :: xs))]
  | Reset (e) -> [IReset (f e xs)]

(* f_t : e -> string list -> i *)
and f_t e xs = match e with
    Num (n) -> [INum n; IReturn]
  | Var (x) -> [IAccess (Env.off_set x xs); IReturn]
  | Op (e0, op, e1) ->
    f e1 xs @ f e0 xs @ [IOp (op); IReturn]
  | Fun (x, e) -> [IGrab (f_t e (x :: xs))]
  | App (e0, e2s) ->
    f_st e2s xs @ f e0 xs @ [IApply]
  | Shift (x, e) -> [IShift (f e (x :: xs)); IReturn]
  | Control (x, e) -> [IControl (f e (x :: xs)); IReturn]
  | Shift0 (x, e) -> [IShift0 (f e (x :: xs)); IReturn]
  | Control0 (x, e) -> [IControl0 (f e (x :: xs)); IReturn]
  | Reset (e) -> [IReset (f e xs); IReturn]

(* f_s : e list -> string list -> i *)
and f_s e2s xs = match e2s with
    [] -> [IPushmark]
  | e :: e2s -> f_s e2s xs @ f e xs

(* f_st : e list -> string list -> i *)
and f_st e2s xs = match e2s with
    [] -> []
  | e :: e2s -> f_st e2s xs @ f e xs

(* f_init : e -> v *)
let f_init expr = run_c ((f expr [], []) :: []) [] TNil MNil

