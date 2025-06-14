(fun a ->
  a +
  (fun c d -> a + c + d)
  ((fun a -> a) 4)
  2
) 1
