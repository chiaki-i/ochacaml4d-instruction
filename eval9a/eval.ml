open Syntax
open Value

(* Definitional interpreter for (λ-calculus with 4 delimited continuation operations : eval1s *)

(* initial continuation : c *)
let idc = C0

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* (>>) : i -> i -> i *)
let (>>) i0 i1 = ISeq (i0, i1)

(* run_c : c -> s -> t -> m -> v *)
let rec run_c c s t m = match (c, s) with
    (C0, v :: []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t), m) -> run_c c (v :: s) t m
        end
      | Trail (h) -> h v TNil m
    end
  | (CSeq (i, vs, c), s) ->
    begin match i with (* CSeq starts here *)
    INum (n) -> run_c c (VNum (n) :: s) t m
  | IAccess (n) -> run_c c (List.nth vs n :: s) t m
  | IOp (op) ->
    begin match s with v :: v0 :: s ->
        begin match (v, v0) with
            (VNum (n0), VNum (n1)) ->
            begin match op with
                Plus -> run_c c (VNum (n0 + n1) :: s) t m
              | Minus -> run_c c (VNum (n0 - n1) :: s) t m
              | Times -> run_c c (VNum (n0 * n1) :: s) t m
              | Divide ->
                if n1 = 0 then failwith "Division by zero"
                else run_c c (VNum (n0 / n1) :: s) t m
            end
          | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
        end
      | _ -> failwith "IOp: unexpected s"
    end
  | ICur (i) ->
    run_c c ((VFun (fun c' (v1 :: s') t' m' ->
      run_c (CSeq (i, (v1 :: vs), c')) s' t' m')) :: s) t m
  | IGrab (i) ->
    begin match s with
        VEmpty :: s ->
        run_c c ((VFun (fun c' (v1 :: s') t' m' ->
          run_c (CSeq (i, (v1 :: vs), c')) s' t' m')) :: s) t m
      | v1 :: s ->
        run_c (CSeq (i, (v1 :: vs), c)) s t m
      | _ -> failwith "IGrab: unexpected s"
    end
  | IApply ->
    begin match s with
        v :: v1 :: s -> app v v1 vs c s t m
      | _ -> failwith "IApply: unexpected s"
    end
  | IReturn ->
    begin match s with
        v :: s -> app_s v vs c s t m
      | _ -> failwith "IReturn: unexpected s"
    end
  | IPushmark -> run_c c (VEmpty :: s) t m
  | ISkip -> run_c c s t m
  | IShift (i) ->
    run_c (CSeq (i, VContS (c, s, t) :: vs, idc)) [] TNil m
  | IControl (i) ->
    run_c (CSeq (i, VContC (c, s, t) :: vs, idc)) [] TNil m
  | IShift0 (i) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        run_c (CSeq (i, VContS (c, s, t) :: vs, c0)) s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | IControl0 (i) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        run_c (CSeq (i, VContC (c, s, t) :: vs, c0)) s0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | IReset (i) ->
    run_c (CSeq (i, vs, idc)) [] TNil (MCons ((c, s, t), m))
  | ISeq (i0, i1) ->
    run_c (CSeq (i0, vs, (CSeq (i1, vs, c)))) s t m
  end
  | _ -> failwith "run_c: stack error"

(* app : v -> v -> v list -> c -> s -> t -> m -> v *)
and app v0 v1 vs c s t m =
  let app_c = CSeq (IReturn, vs, c) in
  match v0 with
    VFun (f) -> f c (v1 :: s) t m
  | VContS (c', s', t') ->
    run_c c' (v1 :: s') t' (MCons ((app_c, s, t), m))
  | VContC (c', s', t') ->
    run_c c' (v1 :: s') (apnd t' (cons (fun v t m -> app_s v vs c s t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* app_s : v -> v list -> c -> s -> t -> m -> v *)
and app_s v0 vs c s t m = match s with
    VEmpty :: s -> run_c c (v0 :: s) t m
  | v1 :: s -> app v0 v1 vs c s t m
  | [] -> failwith "unexpected s"

(* f : definitional interpreter *)
(* f : e -> string list -> i *)
let rec f e xs = match e with
    Num (n) -> INum (n)
  | Var (x) -> IAccess (Env.off_set x xs)
  | Op (e0, op, e1) ->
    f e1 xs >> f e0 xs >> IOp (op)
  | Fun (x, e) -> ICur (f_t e (x :: xs))
  | App (e0, e2s) ->
    f_s e2s xs >> f e0 xs >> IApply
  | Shift (x, e) -> IShift (f e (x :: xs))
  | Control (x, e) -> IControl (f e (x :: xs))
  | Shift0 (x, e) -> IShift0 (f e (x :: xs))
  | Control0 (x, e) -> IControl0 (f e (x :: xs))
  | Reset (e) -> IReset (f e xs)

(* f_t : e -> string list -> i *)
and f_t e xs = match e with
    Num (n) -> INum n >> IReturn
  | Var (x) -> IAccess (Env.off_set x xs) >> IReturn
  | Op (e0, op, e1) ->
    f e1 xs >> f e0 xs >> IOp (op) >> IReturn
  | Fun (x, e) -> IGrab (f_t e (x :: xs))
  | App (e0, e2s) ->
    f_st e2s xs >> f e0 xs >> IApply
  | Shift (x, e) -> IShift (f e (x :: xs)) >> IReturn
  | Control (x, e) -> IControl (f e (x :: xs)) >> IReturn
  | Shift0 (x, e) -> IShift0 (f e (x :: xs)) >> IReturn
  | Control0 (x, e) -> IControl0 (f e (x :: xs)) >> IReturn
  | Reset (e) -> IReset (f e xs) >> IReturn

(* f_s : e list -> string list -> i *)
and f_s e2s xs = match e2s with
    [] -> IPushmark
  | e :: e2s -> f_s e2s xs >> f e xs

(* f_st : e list -> string list -> i *)
and f_st e2s xs = match e2s with
    [] -> ISkip (* 空の命令として残すが、リスト化すると消せる *)
  | e :: e2s -> f_st e2s xs >> f e xs

(* f_init : e -> v *)
let f_init expr = run_c (CSeq (f expr [], [], idc)) [] TNil MNil

