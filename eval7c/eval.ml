open Syntax
open Value

(* Defunctionalized interpreter with values passed via stack : eval7d wo r.s.*)
(* refunctionalize c' *)

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* run_c7 : c -> s -> t -> m -> v *)
let rec run_c7 c s t m = match (c, s) with
    (C0, v :: []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t), m) -> run_c7 c (v :: s) t m
        end
      | Trail (h) -> h v TNil m
    end
  | (CSeq (c', vs, c), (v :: s)) ->
    c' vs c (v :: s) t m

(* apply7 : v -> v -> c -> s -> t -> m -> v *)
let apply7 v0 v1 c s t m = match v0 with
    VFun (f) -> f c (v1 :: s) t m
  | VContS (c', s', t') -> run_c7 c' (v1 :: s') t' (MCons ((c, s, t), m))
  | VContC (c', s', t') ->
    run_c7 c' (v1 :: s')
           (apnd t' (cons (fun v t m -> run_c7 c (v :: s) t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* apply7s : v -> v list -> v list -> c -> s -> t -> m -> v *)
let rec apply7s v0 v2s vs c s t m = match v2s with
    [] -> run_c7 c (v0 :: s) t m
  | v1 :: v2s ->
    apply7 v0 v1 (CSeq ((fun vs c (v :: VArgs (v2s) :: s) t m ->
      apply7s v v2s vs c s t m), vs, c)) (VArgs (v2s) :: s) t m

(* apply : c' *)
let apply = fun vs c s t m -> match s with
  v0 :: VArgs (v2s) :: s -> apply7s v0 v2s vs c s t m

(* f7 : e -> string list -> v list -> c -> s -> t -> m -> v *)
let rec f7 e xs vs c s t m = match e with
    Num (n) -> run_c7 c (VNum (n) :: s) t m
  | Var (x) -> run_c7 c (List.nth vs (Env.offset x xs) :: s) t m
  | Op (e0, op, e1) ->
    f7 e1 xs vs (CSeq ((fun vs c (v1 :: s) t m ->
      f7 e0 xs vs (CSeq ((fun vs c (v0 :: v1 :: s) t m ->
        begin match (v0, v1) with
            (VNum (n0), VNum (n1)) ->
            begin match op with
                Plus -> run_c7 c (VNum (n0 + n1) :: s) t m
              | Minus -> run_c7 c (VNum (n0 - n1) :: s) t m
              | Times -> run_c7 c (VNum (n0 * n1) :: s) t m
              | Divide ->
                if n1 = 0 then failwith "Division by zero"
                else run_c7 c (VNum (n0 / n1) :: s) t m
            end
          | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                           ^ " are not numbers")
        end
      ), vs, c)) (v1 :: s) t m), vs, c)) s t m
  | Fun (x, e) ->
    begin match (c, s) with
      (CSeq (i', vs', c'), VArgs (v1 :: v2s) :: s') when i' == apply -> (*Grab*)
             f7 e (x :: xs) (v1 :: vs)
                  (CSeq (i', vs', c')) (VArgs (v2s) :: s') t m
    | _ -> run_c7 c (VFun (fun c' (v1 :: s') t' m' ->
             f7 e (x :: xs) (v1 :: vs) c' s' t' m') :: s) t m
    end
  | App (e0, e2s) ->
    f7s e2s xs vs (CSeq ((fun vs c (VArgs (v2s) :: s) t m ->
      f7 e0 xs vs (CSeq ((fun vs c (v :: VArgs (v2s) :: s) t m ->
        apply7s v v2s vs c s t m), vs, c)) (VArgs (v2s) :: s) t m
    ), vs, c)) s t m
  | Shift (x, e) -> f7 e (x :: xs) (VContS (c, s, t) :: vs) C0 [] TNil m
  | Control (x, e) -> f7 e (x :: xs) (VContC (c, s, t) :: vs) C0 [] TNil m
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
  | Reset (e) -> f7 e xs vs C0 [] TNil (MCons ((c, s, t), m))

(* f7s : e list -> string list -> v list -> c -> s -> t -> m -> v list *)
and f7s e2s xs vs c s t m = match e2s with
    [] -> run_c7 c (VArgs ([]) :: s) t m
  | e :: e2s ->
    f7s e2s xs vs (CSeq ((fun vs c (VArgs (v2s) :: s) t m ->
      f7 e xs vs (CSeq ((fun vs c (v :: VArgs (v2s) :: s) t m ->
        run_c7 c (VArgs (v :: v2s) :: s) t m
      ), vs, c)) (VArgs (v2s) :: s) t m
    ), vs, c)) s t m

(* f : e -> v *)
let f expr = f7 expr [] [] C0 [] TNil MNil
