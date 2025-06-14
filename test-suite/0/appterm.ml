(fun f -> (fun z -> f (z + 4)) 2 3) (fun x -> fun y -> x * y)
