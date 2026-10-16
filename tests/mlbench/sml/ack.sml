fun ack (m,n) =
    if m = 0 then n+1
    else if n = 0 then ack (m - 1, 1)
    else ack(m - 1, ack (m, n - 1))
fun loop (n, acc) = if n = 0 then acc else loop (n - 1, acc + ack (3, 11) + ack (2, 5))
val _ = print (Int.toString (loop (1, 0)) ^ "\n")
