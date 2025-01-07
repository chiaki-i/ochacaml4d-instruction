reset (reset
  ((control0 h -> 3 * (h 2)) + (control0 g -> (fun x -> x + 1) (g 4))))

(* left-to-right *)
(* < < (F0h. 3 * h 2) + (F0g. (\x. x + 1) (g 4)) > > *)
(* < 3 * h 2 > where h = \x. x + (F0g. (\x. x + 1) (g 4)) *)
(* < 3 * (2 + (F0g. (\x. x + 1) (g 4))) > *)
(* (\x. x + 1) (g 4) where g = \x. 3 * (2 + x) *)
(* (\x. x + 1) (3 * (2 + 4)) *)
(* 19 *)

(* right-to-left *)
(* < < (F0h. 3 * h 2) + (F0g. (\x. x + 1) (g 4)) > > *)
(* < (\x. x + 1) (g 4) > where g = \x. (F0h. 3 * h 2) + x *)
(* < (\x. x + 1) ((F0h. 3 * h 2) + 4) > *)
(* 3 * h 2 where h = \x. (\x. x + 1) (x + 4) *)
(* 3 * (\x. x + 1) (2 + 4) *)
(* 21 *)
