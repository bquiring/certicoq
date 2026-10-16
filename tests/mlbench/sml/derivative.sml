datatype expr = Add of expr list | Sub of expr list | Mul of expr list | Div of expr list | Num of int | X

fun foldlEq f init (l1, l2) = let
      fun foldf (xs, ys, accum) = (case (xs, ys)
             of (x::xs, y::ys) => foldf(xs, ys, f(x, y, accum))
              | ([], []) => accum
              | _ => false)
      in foldf (l1, l2, init) end

fun equal p = (case p
       of (X, X) => true
        | (Num a, Num b) => a = b
        | (Add xs, Add ys) => chkLists (xs, ys)
        | (Sub xs, Sub ys) => chkLists (xs, ys)
        | (Mul xs, Mul ys) => chkLists (xs, ys)
        | (Div xs, Div ys) => chkLists (xs, ys)
        | _ => false)
and chkLists p = foldlEq chk true p
and chk (a, b, acc) = acc andalso equal (a, b)

fun map f [] = [] | map f (x :: xs) = f x :: map f xs

fun deriv a = (case a
       of X => Num 1
        | Num _ => Num 0
        | Add es => Add (map deriv es)
        | Sub es  => Sub (map deriv es)
        | Mul es  => Mul [a, Add (map (fn x => Div [deriv x, x]) es)]
        | Div[x, y] => Sub [Div [deriv x, y], Div [x, Mul [y, y, deriv y]]]
        | _ => X)

fun b2i b = if b then 1 else 0

fun doit () = let
      fun mkExp a b = Sub [Add [Mul [Num 3, X, X], Mul [a, X, X], Mul [b, X], Num 5], X]
      fun mkAns a b = Sub [Add [
              Mul [Mul [Num 3, X, X], Add [Div [Num 0, Num 3], Div [Num 1, X], Div [Num 1, X]]],
              Mul [Mul [a, X, X], Add [Div [Num 0, a], Div [Num 1, X], Div [Num 1, X]]],
              Mul [Mul [b, X], Add [Div [Num 0, b], Div [Num 1, X]]],
              Num 0], Num 1]
      val a = Num 5
      val b = Num 7
      val exp = mkExp a b
      val ans = mkAns a b
      in
        b2i (equal (ans, deriv ans)) + b2i (equal (ans, deriv ans)) +
        b2i (equal (Num 2, Num 1)) + b2i (equal (X, Num 1)) + b2i (equal (Add [], Sub [])) +
        b2i (equal (ans, deriv exp))
      end

fun loop (n, acc) = if n = 0 then acc else loop (n - 1, acc + doit ())
val _ = print (Int.toString (loop (262144, 0)) ^ "\n")
