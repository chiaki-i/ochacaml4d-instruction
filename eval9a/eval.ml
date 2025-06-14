open Syntax
open Value

(* defunctionalize eval8st: eval9st *)

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
    begin match s with
        VEmpty :: s ->
        run_c9 c ((VFun (fun c' (v1 :: s') t' m' ->
          run_c9 (CSeq (i, (v1 :: vs), c')) s' t' m')) :: s) t m
      | v1 :: s ->
        run_c9 (CSeq (i, (v1 :: vs), c)) s t m
      | _ -> failwith "IGrab: unexpected s"
    end
  | IApply ->
    begin match s with (v :: v1 :: s) ->
        apply9 v v1 vs c s t m
      | _ -> failwith "IApply: unexpected s"
    end
  | IPushmark -> run_c9 c (VEmpty :: s) t m
  | IReturn ->
    begin match s with (v :: s) ->
        apply9s v vs c s t m
      | _ -> failwith "IReturn: unexpected s"
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

(* apply9 : v -> v -> v list -> c -> s -> t -> m -> v *)
and apply9 v0 v1 vs c s t m =
  match v0 with
    VFun (f) -> f c (v1 :: s) t m
  | VContS (c', s', t') ->
    let app_c = CSeq (IReturn, vs, c) in
    run_c9 c' (v1 :: s') t' (MCons ((app_c, s, t), m))
  | VContC (c', s', t') ->
    let app_c = CSeq (IReturn, vs, c) in
    run_c9 c' (v1 :: s') (apnd t' (cons (fun v t m -> run_c9 app_c (v :: s) t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* apply9s : v -> v list -> c -> s -> t -> m -> v *)
and apply9s v0 vs c s t m = match s with
    VEmpty :: s -> run_c9 c (v0 :: s) t m
  | v1 :: s -> apply9 v0 v1 vs c s t m

(* (>>) : i -> i -> i *)
let (>>) i0 i1 = ISeq (i0, i1)

(* f9: e -> string list -> i *)
let rec f9 e xs = match e with
    Num (n) -> INum (n)
  | Var (x) -> IAccess (Env.offset x xs)
  | Op (e0, op, e1) ->
    f9 e1 xs >> f9 e0 xs >> IOp (op)
  | Fun (x, e) -> ICur (f9t e (x :: xs))
  | App (e0, e2s) ->
    f9s e2s xs >> f9 e0 xs >> IApply
  | Shift (x, e) -> IShift (f9 e (x :: xs))
  | Control (x, e) -> IControl (f9 e (x :: xs))
  | Shift0 (x, e) -> IShift0 (f9 e (x :: xs))
  | Control0 (x, e) -> IControl0 (f9 e (x :: xs))
  | Reset (e) -> IReset (f9 e xs)

(* f9s : e list -> string list -> v list -> c -> s -> t -> m -> v list *)
and f9s e2s xs = match e2s with
    [] -> IPushmark
  | e :: e2s -> f9s e2s xs >> f9 e xs

(* f9t : e -> string list -> v list -> c -> s -> t -> m -> v *)
and f9t e xs = match e with
    Num (n) -> INum n >> IReturn
  | Var (x) -> IAccess (Env.offset x xs) >> IReturn
  | Op (e0, op, e1) ->
    f9 e1 xs >> f9 e0 xs >> IOp (op) >> IReturn
  | Fun (x, e) -> IGrab (f9t e (x :: xs))
  | App (e0, e2s) -> f9s e2s xs >> f9 e0 xs >> IApply >> IReturn
  | Shift (x, e) -> IShift (f9 e (x :: xs)) >> IReturn
  | Control (x, e) -> IControl (f9 e (x :: xs)) >> IReturn
  | Shift0 (x, e) -> IShift0 (f9 e (x :: xs)) >> IReturn
  | Control0 (x, e) -> IControl0 (f9 e (x :: xs)) >> IReturn
  | Reset (e) -> IReset (f9 e xs) >> IReturn

(* f : e -> v *)
let f expr = run_c9 (CSeq (f9 expr [], [], C0)) [] TNil MNil
