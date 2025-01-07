reset (reset (1 + reset ((fun y -> (control h -> h y))
                         (control f -> (control g -> 2 * f (g 5))))))
