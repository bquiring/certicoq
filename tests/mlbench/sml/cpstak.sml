fun cpstak (x, y, z) =
  let fun tak (x, y, z, k) =
        if (y >= x) then k z
        else tak (x - 1, y, z, fn (v1) =>
               tak (y - 1, z, x, fn (v2) =>
                 tak (z - 1, x, y, fn (v3) => tak (v1, v2, v3, k))))
  in tak (x, y, z, fn a => a) end
fun loop (n, acc) = if n = 0 then acc else loop (n - 1, acc + cpstak (14, 11, 0))
val _ = print (Int.toString (loop (8, 0)) ^ "\n")
