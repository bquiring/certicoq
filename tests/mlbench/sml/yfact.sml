fun y f x = let fun g x = y f x in f g x end
fun factY fact n = if n = 0 then 1 else n * fact (n - 1)
val fact = y factY
fun loop (n, acc) = if n = 0 then acc else loop (n - 1, acc + fact 11 + fact 10)
val _ = print (Int.toString (loop (2097152, 0)) ^ "\n")
