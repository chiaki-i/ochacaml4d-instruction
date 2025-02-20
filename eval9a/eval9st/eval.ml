open Syntax
open Value

(* defunctionalize eval8st: eval9st *)

(* initial continuation *)
let idc = C0

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

let rec run_c9 c s t m = match (c, s) with
    (C0, v :: []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t), m) -> run_c9 c (v :: s) t m
        end
      | Trail (h) -> h v TNil m
    end
  | (CSeq (i, vs, c), s) ->
    begin match i with (* CSeq starts here *)
    INum (n) -> run_c9 c (VNum (n) :: s) t m
  | IAccess (n) -> run_c9 c (List.nth vs n :: s) t m
  | IOp (op) ->
    begin match s with v :: v0 :: s ->
        begin match (v, v0) with
            (VNum (n0), VNum (n1)) ->
            begin match op with
                Plus -> run_c9 c (VNum (n0 + n1) :: s) t m
              | Minus -> run_c9 c (VNum (n0 - n1) :: s) t m
              | Times -> run_c9 c (VNum (n0 * n1) :: s) t m
              | Divide ->
                if n1 = 0 then failwith "Division by zero"
                else run_c9 c (VNum (n0 / n1) :: s) t m
            end
          | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
        end
      | _ -> failwith "IOp: unexpected s"
    end
  | ICur (i) ->
    run_c9 c ((VFun (fun c' (v1 :: s') t' m' ->
      run_c9 (CSeq (i, (v1 :: vs), c')) s' t' m')) :: s) t m
  | IGrab (i) ->
    begin match s with (VArgs (v2s) :: s) ->
        begin match v2s with
          [] ->
          run_c9 c ((VFun (fun c' (v1 :: s') t' m' ->
            run_c9 (CSeq (i, (v1 :: vs), c')) s' t' m')) :: s) t m
        | v1 :: v2s ->
          run_c9 (CSeq (i, (v1 :: vs), (CSeq (IApply, vs, c)))) (VArgs (v2s) :: s) t m
        end
      | _ -> failwith "IGrab: unexpected s"
    end
  | IApply ->
    begin match s with (v :: VArgs (v2s) :: s) ->
        apply9s v v2s vs c s t m
      | _ -> failwith "IApply: unexpected s"
    end
  | IAppterm (i) ->
    run_c9 (CSeq (i, vs, CSeq (IApply, vs, c))) s t m
  | IPushmark -> run_c9 c (mark :: s) t m
  | IPush ->
    begin match s with v :: VArgs (v2s) :: s ->
        run_c9 c (VArgs (v :: v2s) :: s) t m
      | _ -> failwith "IPush: unexpected s"
    end
  | IShift (i) ->
    run_c9 (CSeq (i, VContS (c, s, t) :: vs, idc)) [] TNil m
  | IControl (i) ->
    run_c9 (CSeq (i, VContC (c, s, t) :: vs, idc)) [] TNil m
  | IShift0 (i) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        run_c9 (CSeq (i, VContS (c, s, t) :: vs, c0)) s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | IControl0 (i) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        run_c9 (CSeq (i, VContC (c, s, t) :: vs, c0)) s0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | IReset (i) ->
    run_c9 (CSeq (i, vs, C0)) [] TNil (MCons ((c, s, t), m))
  | ISeq (i0, i1) ->
    run_c9 (CSeq (i0, vs, (CSeq (i1, vs, c)))) s t m
  end
  | _ -> failwith "run_c9: stack error"

(* apply9 : v -> v -> c -> s -> t -> m -> v *)
and apply9 v0 v1 c s t m = match v0 with
    VFun (f) -> f c (v1 :: s) t m
  | VContS (c', s', t') -> run_c9 c' (v1 :: s') t' (MCons ((c, s, t), m))
  | VContC (c', s', t') ->
    run_c9 c' (v1 :: s') (apnd t' (cons (fun v t m -> run_c9 c (v :: s) t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* apply9s : v -> v list -> c -> s -> t -> m -> v *)
and apply9s v0 v2s vs c s t m = match v2s with
    [] -> run_c9 c (v0 :: s) t m
  | v1 :: v2s ->
    apply9 v0 v1 (CSeq (IApply, vs, c)) (VArgs (v2s) :: s) t m

(* (>>) : i -> i -> i *)
let (>>) i0 i1 = ISeq (i0, i1)

(* f9: e -> string list -> i *)
let rec f9 e xs = match e with
    Num (n) -> INum (n)
  | Var (x) -> IAccess (Env.offset x xs)
  | Op (e0, op, e1) ->
    f9 e1 xs >> f9 e0 xs >> IOp (op)
  | Fun (x, e) -> ICur (f9 e (x :: xs))
  | App (e0, e2s) ->
    f9s e2s xs >> f9t e0 xs
  | Shift (x, e) -> IShift (f9 e (x :: xs))
  | Control (x, e) -> IControl (f9 e (x :: xs))
  | Shift0 (x, e) -> IShift0 (f9 e (x :: xs))
  | Control0 (x, e) -> IControl0 (f9 e (x :: xs))
  | Reset (e) -> IReset (f9 e xs)

(* f9s : e list -> string list -> v list -> c -> s -> t -> m -> v list *)
and f9s e2s xs = match e2s with
    [] -> IPushmark
  | e :: e2s -> f9s e2s xs >> f9 e xs >> IPush

(* f9t : e -> string list -> v list -> c -> s -> t -> m -> v *)
and f9t e xs = match e with
    Num (n) -> INum n >> IApply
  | Var (x) -> IAccess (Env.offset x xs) >> IApply
  | Op (e0, op, e1) ->
    f9 e1 xs >> f9 e0 xs >> IOp (op) >> IApply
  | Fun (x, e) -> IGrab (f9 e (x :: xs))
  | App (e0, e2s) -> f9s e2s xs >> IAppterm (f9t e0 xs)
  | Shift (x, e) -> IShift (f9 e (x :: xs)) >> IApply
  | Control (x, e) -> IControl (f9 e (x :: xs)) >> IApply
  | Shift0 (x, e) -> IShift0 (f9 e (x :: xs)) >> IApply
  | Control0 (x, e) -> IControl0 (f9 e (x :: xs)) >> IApply
  | Reset (e) -> IReset (f9 e xs) >> IApply

(* f : e -> v *)
let f expr = run_c9 (CSeq (f9 expr [], [], C0)) [] TNil MNil
