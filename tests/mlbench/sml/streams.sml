(*
signature PULL = sig
  type ('s, 'a) t

  val empty : (unit, 'a) t
  val repeat : 'a -> ('a, 'a) t
  val fromList : 'a list -> ('a list, 'a) t
  val unfold : ('s -> ('a * 's) option) -> 's -> ('s, 'a) t
  val zipWith : ('a * 'b -> 'c) -> ('s1, 'a) t * ('s2, 'b) t -> ('s1 * 's2 * 'a option, 'c) t
  val map : ('a -> 'b) -> ('s, 'a) t -> ('s, 'b) t
  val take : ('s, 'a) t * int -> ('s * int, 'a) t
  val filter : ('a -> bool) -> ('s, 'a) t -> ('s, 'a) t
  val foldl : ('a * 'b -> 'b) -> 'b -> ('s, 'a) t -> 'b
end
*)

structure Pull (* : PULL *) = struct

  datatype ('a, 's) step
    = Yield of 'a * 's
    | Skip of 's
    | Done

  datatype ('s, 'a) t = Pull of 's * ('s -> ('a, 's) step)

  (* val empty = Pull ((), fn () => Done) *)

  fun repeat x = Pull (x, fn x => Yield (x, x))

  fun fromList xs = Pull (xs, fn [] => Done | x :: xs => Yield (x, xs))

  fun unfold next seed =
    let
      fun step s =
        case next s of
            NONE => Done
          | SOME (a, s') => Yield (a, s')
    in
      Pull (seed, step)
    end

  fun zipWith f (Pull (s1, step1), Pull (s2, step2)) =
    let
      fun step (s1, s2, NONE) =
        (case step1 s1 of
            Done => Done
          | Skip s1 => Skip (s1, s2, NONE)
          | Yield (a, s1) => Skip (s1, s2, SOME a))
        | step (s1, s2, SOME a) =
        (case step2 s2 of
            Done => Done
          | Skip s2 => Skip (s1, s2, SOME a)
          | Yield (b, s2) => Yield (f (a, b), (s1, s2, NONE)))
    in
      Pull ((s1, s2, NONE), step)
    end

  fun map f (Pull (s, step)) =
    Pull (s, fn s => case step s of
                        Done => Done
                      | Skip s' => Skip s'
                      | Yield (a, s') => Yield (f a, s'))

  fun take (Pull (s, step), n) =
    Pull ((s, n), fn (s, n) =>
      if n <= 0 then Done else
      case step s of
          Done => Done
        | Skip s' => Skip (s', n)
        | Yield (a, s') => Yield (a, (s', n - 1)))

  fun filter p (Pull (s, step)) =
    Pull (s, fn s =>
      case step s of
          Done => Done
        | Skip s' => Skip s'
        | Yield (a, s') => if p a then Yield (a, s') else Skip s')

  fun foldl f acc (Pull (s, step)) =
    let
      fun go (s, acc) =
        case step s of
            Done => acc
          | Skip s' => go (s', acc)
          | Yield (a, s') => go (s', f (a, acc))
    in
      go (s, acc)
    end
end

(*
signature PUSH = sig

  type ('s, 'a) t

  val empty : ('s, 'a) t
  val cons : 'a * ('s, 'a) t -> ('s, 'a) t
  val singleton : 'a -> ('s, 'a) t
  val fromList : 'a list -> ('s, 'a) t
  val fromPull : ('s1, 'a) Pull.t -> ('s, 'a) t
  val countFrom : int -> ('s, int) t
  val map : ('a -> 'b) -> ('s, 'a) t -> ('s, 'b) t
  val concatMap : ('a -> ('s, 'b) t) -> ('s, 'a) t -> ('s, 'b) t
  val zipWith : ('a * 'b -> 'c) -> ('s2 -> 's3, 'a) t -> ('s2, 'b) Pull.t -> ('s3, 'c) t
  val foldl : ('a * 'b -> 'b) -> 'b -> ('b, 'a) t -> 'b
end
*)

structure Push (* : PUSH *) = struct

  type ('s, 'a) t = ('a * (unit -> 's) -> 's) * (unit -> 's) -> 's

  fun empty (_, n) = n ()

  fun cons (x, k) (c, n) = c (x, fn _ => k (c, n))

  fun singleton x (c, n) = c (x, n)

  fun fromList xs (c, n) =
    let
      fun go [] = n ()
        | go (x :: xs) = c (x, fn _ => go xs)
    in
      go xs
    end

  fun fromPull (Pull.Pull (s, step)) (c, n) =
    let
      fun go s =
        case step s of
            Pull.Done => n ()
          | Pull.Skip s' => go s'
          | Pull.Yield (a, s') => c (a, fn _ => go s')
    in
      go s
    end

  fun countFrom i (c, _) =
    let
      fun go i = c (i, fn _ => go (i + 1))
    in
      go i
    end

  fun map f k (c, n) = k (fn (a, s) => c (f a, s), n)

  fun concatMap f k (c, n) =
    k (fn (a, s) => f a (c, s), n)

  fun zipWith f k (Pull.Pull (seed, step)) (c, n) =
    k (fn (a, hyp) => fn s =>
        case step s of
            Pull.Done => hyp () s
          | Pull.Skip s' => hyp () s'
          | Pull.Yield (b, s') => c (f (a, b), fn () => hyp () s'),
       fn () => fn _ => n ())
      seed

  fun foldl f acc k = k (fn (a, s) => f (a, s ()), fn _ => acc)
end

fun countFrom n =
  Pull.unfold (fn n => SOME (n, n + 1)) n

fun complex (xs, ys) =
  let
    val xs = Pull.fromList xs
    val xs = Pull.map (fn x => x * x) xs
    val xs = Pull.take (xs, 12)
    val xs = Pull.filter (fn n => n mod 2 = 0) xs
    val xs = Pull.map (fn x => x * x) xs

    val ys = Push.fromList ys
    (* val ys = Push.take (ys, 3) *)
    (* val ys = Push.filter (fn n => n mod 2 = 0) ys *)

    val s = Push.zipWith (fn p => p) ys xs
  in
    Push.foldl op :: [] s
  end

val s1 = [1, 2, 3, 4, 5, 6]
val s2 = [10, 20, 30, 40, 50, 60]
fun sumPairs (xs, acc) = case xs of [] => acc | (a, b) :: r => sumPairs (r, acc + a + b)
fun loop (n, acc) = if n = 0 then acc else loop (n - 1, sumPairs (complex (s1, s2), acc))
val _ = print (Int.toString (loop (8388608, 0)) ^ "\n")
