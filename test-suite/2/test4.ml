(fun x -> (reset (reset (x * reset ((fun y -> control h -> y)
                                    (control f -> control g -> 2 + f 5)))))) 7
