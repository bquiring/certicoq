fun tak (x, y, z) = if y < x then tak(tak(x-1, y, z), tak(y-1, z, x), tak(z-1, x, y)) else z
fun loop (n, acc) = if n = 0 then acc else loop (n - 1, acc + tak (14, 11, 0))
val _ = print (Int.toString (loop (8, 0)) ^ "\n")
