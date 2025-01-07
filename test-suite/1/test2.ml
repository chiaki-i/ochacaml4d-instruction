reset ((shift h -> 3 * (h 2)) + (shift g -> (fun x -> x + 1) (g 4)))

(* left-to-right *)
(* < (Sh. 3 * h 2) + (Sg. (\x. x + 1) (g 4)) > *)
(* < 3 * h 2 > where h = \x. < x + (Sg. (\x. x + 1) (g 4)) > *)
(* < 3 * < 2 + (Sg. (\x. x + 1) (g 4)) > > *)
(* < 3 * < (\x. x + 1) (g 4) > > where g = \x. < 2 + x > *)
(* < 3 * < (\x. x + 1) < 2 + 4 > > > *)
(* 21 *)

(* right-to-left *)
(* < (Sh. 3 * h 2) + (Sg. (\x. x + 1) (g 4)) > *)
(* < (\x. x + 1) (g 4) > where g = \x. < (Sh. 3 * h 2) + x > *)
(* < (\x. x + 1) < (Sh. 3 * h 2) + 4 > > *)
(* < (\x. x + 1) < 3 * h 2 > > where h = \x. < x + 4 > *)
(* < (\x. x + 1) < 3 * < 2 + 4 > > > *)
(* 19 *)