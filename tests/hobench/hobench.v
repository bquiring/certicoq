(* Higher-order benchmarks for the web optimizations.

   Each program returns a primitive integer, which the C driver prints.
   They are written so that closures survive the -O 1 pipeline: functions
   are stored in data structures, passed to recursive higher-order
   functions at several call sites, or built as continuations. *)

From Stdlib Require Import PrimInt63 Uint63 List.
From CertiRocq.Plugin Require Import CertiRocq.

Import ListNotations.
Open Scope uint63_scope.

(* Fuel for recursions that are not structural *)
Definition fuel0 : nat := 4000.

(* Loop [n] times *)
Fixpoint loop {A} (n : nat) (f : A -> A) (x : A) : A :=
  match n with
  | O => x
  | S n => loop n f (f x)
  end.

Fixpoint range (n : nat) (i : int) : list int :=
  match n with
  | O => []
  | S n => i :: range n (i + 1)
  end.

Definition sum (l : list int) : int := fold_left (fun a x => a + x) l 0.

(** * cps: continuation-passing traversals of a tree *)

Inductive tree := Leaf (x : int) | Node (l r : tree).

Fixpoint build (d : nat) (x : int) : tree :=
  match d with
  | O => Leaf x
  | S d => Node (build d (2 * x)) (build d (2 * x + 1))
  end.

Fixpoint sum_k {A} (t : tree) (k : int -> A) : A :=
  match t with
  | Leaf x => k x
  | Node l r => sum_k l (fun a => sum_k r (fun b => k (a + b)))
  end.

Fixpoint max_k {A} (t : tree) (k : int -> A) : A :=
  match t with
  | Leaf x => k x
  | Node l r => max_k l (fun a => max_k r (fun b => k (if a <? b then b else a)))
  end.

Fixpoint leaves_k {A} (t : tree) (acc : list int) (k : list int -> A) : A :=
  match t with
  | Leaf x => k (x :: acc)
  | Node l r => leaves_k r acc (fun acc => leaves_k l acc k)
  end.

Definition cps :=
  let t := build 14 1 in
  loop 4 (fun acc => acc + sum_k t (fun x => x) + max_k t (fun x => x)
                     + leaves_k t [] (fun l => sum l)) 0.

(** * parse: parser combinators over a token list *)

Inductive token := TNum (n : int) | TPlus | TTimes | TLP | TRP.

Definition parser A := list token -> option (A * list token).

Definition ret {A} (a : A) : parser A := fun ts => Some (a, ts).
Definition bind {A B} (p : parser A) (f : A -> parser B) : parser B :=
  fun ts => match p ts with Some (a, ts) => f a ts | None => None end.
Definition alt {A} (p q : parser A) : parser A :=
  fun ts => match p ts with Some r => Some r | None => q ts end.
Definition tok (t : token) : parser unit :=
  fun ts =>
    match ts, t with
    | TPlus :: ts, TPlus | TTimes :: ts, TTimes | TLP :: ts, TLP | TRP :: ts, TRP => Some (tt, ts)
    | _, _ => None
    end.
Definition num : parser int :=
  fun ts => match ts with TNum n :: ts => Some (n, ts) | _ => None end.

(* [a op a op ... a], folded with [f] *)
Fixpoint chain (fuel : nat) (p : parser int) (op : parser unit) (f : int -> int -> int) (acc : int) : parser int :=
  match fuel with
  | O => ret acc
  | S fuel => alt (bind op (fun _ => bind p (fun b => chain fuel p op f (f acc b)))) (ret acc)
  end.

Fixpoint expr (fuel : nat) : parser int :=
  match fuel with
  | O => fun _ => None
  | S fuel =>
      let atom := alt num (bind (tok TLP) (fun _ => bind (expr fuel) (fun e => bind (tok TRP) (fun _ => ret e)))) in
      let term := bind atom (fun a => chain 1000 atom (tok TTimes) PrimInt63.mul a) in
      bind term (fun a => chain 1000 term (tok TPlus) PrimInt63.add a)
  end.

(* (1 * 2 + 3) * (4 + 5 * 6) + ... *)
Fixpoint gen (n : nat) (i : int) : list token :=
  match n with
  | O => [TNum i]
  | S n => TLP :: TNum i :: TTimes :: TNum (i + 1) :: TPlus :: TNum (i + 2) :: TRP :: TTimes
             :: TLP :: TNum (i + 3) :: TPlus :: TNum (i + 4) :: TRP :: TPlus :: gen n (i + 5)
  end.

Definition parse :=
  let ts := gen 300 1 in
  loop 20 (fun acc => match expr 4 ts with Some (v, []) => acc + v | _ => acc end) 0.

(** * relabel: a state monad *)

Definition st A := int -> A * int.
Definition sret {A} (a : A) : st A := fun s => (a, s).
Definition sbind {A B} (m : st A) (f : A -> st B) : st B := fun s => let (a, s) := m s in f a s.
Definition fresh : st int := fun s => (s, s + 1).

Fixpoint relabel (t : tree) : st tree :=
  match t with
  | Leaf _ => sbind fresh (fun n => sret (Leaf n))
  | Node l r => sbind (relabel l) (fun l => sbind (relabel r) (fun r => sret (Node l r)))
  end.

Fixpoint mapM {A B} (f : A -> st B) (l : list A) : st (list B) :=
  match l with
  | [] => sret []
  | x :: l => sbind (f x) (fun y => sbind (mapM f l) (fun l => sret (y :: l)))
  end.

Fixpoint tsum (t : tree) : int :=
  match t with Leaf x => x | Node l r => tsum l + tsum r end.

Definition relabel_bench :=
  let t := build 13 0 in
  loop 4 (fun acc =>
    let '(t', s) := relabel t acc in
    let '(l, s) := mapM (fun x => sbind fresh (fun n => sret (x * n))) (range 2000 0) s in
    tsum t' + sum l + s) 0.

(** * compile: an expression compiled to closures over an environment *)

Inductive ex :=
| Var (n : nat) | Lit (n : int) | Add (a b : ex) | Mul (a b : ex)
| Let (a b : ex)                (* binds variable 0 in [b] *)
| If0 (a b c : ex).

Definition env := nat -> int.
Definition push (v : int) (rho : env) : env := fun n => match n with O => v | S n => rho n end.

Fixpoint comp (e : ex) : env -> int :=
  match e with
  | Var n => fun rho => rho n
  | Lit n => fun _ => n
  | Add a b => let a := comp a in let b := comp b in fun rho => a rho + b rho
  | Mul a b => let a := comp a in let b := comp b in fun rho => a rho * b rho
  | Let a b => let a := comp a in let b := comp b in fun rho => b (push (a rho) rho)
  | If0 a b c => let a := comp a in let b := comp b in let c := comp c in
                 fun rho => if a rho =? 0 then b rho else c rho
  end.

Fixpoint prog (n : nat) : ex :=
  match n with
  | O => Add (Var 0) (Var 1)
  | S n => Let (Add (Mul (Var 0) (Lit 3)) (Var 1))
               (If0 (Var 2) (prog n) (Add (prog n) (Lit 1)))
  end.

Definition compile :=
  let f := comp (prog 8) in
  fold_left (fun acc i => acc + f (push i (push (i + 7) (fun _ => 0)))) (range 1000 0) 0.

(** * stream: lazy streams with closures as thunks, a sieve of filters *)

Inductive stream := SNil | SCons (x : int) (tl : unit -> stream).

Fixpoint from (fuel : nat) (i : int) : stream :=
  match fuel with O => SNil | S fuel => SCons i (fun _ => from fuel (i + 1)) end.

Fixpoint sfilter (fuel : nat) (p : int -> bool) (s : stream) : stream :=
  match fuel with
  | O => SNil
  | S fuel =>
      match s with
      | SNil => SNil
      | SCons x tl => if p x then SCons x (fun _ => sfilter fuel p (tl tt)) else sfilter fuel p (tl tt)
      end
  end.

Fixpoint smap (fuel : nat) (f : int -> int) (s : stream) : stream :=
  match fuel with
  | O => SNil
  | S fuel => match s with SNil => SNil | SCons x tl => SCons (f x) (fun _ => smap fuel f (tl tt)) end
  end.

Fixpoint sieve (fuel : nat) (s : stream) : stream :=
  match fuel with
  | O => SNil
  | S fuel =>
      match s with
      | SNil => SNil
      | SCons p tl => SCons p (fun _ => sieve fuel (sfilter fuel0 (fun x => negb (x mod p =? 0)) (tl tt)))
      end
  end.

Fixpoint stake (n : nat) (s : stream) : list int :=
  match n with
  | O => []
  | S n => match s with SNil => [] | SCons x tl => x :: stake n (tl tt) end
  end.

Definition stream_bench :=
  sum (stake 300 (smap fuel0 (fun x => x * x) (sieve fuel0 (from fuel0 2)))).

(** * queens: backtracking with success and failure continuations *)

Fixpoint safe (q : int) (d : int) (qs : list int) : bool :=
  match qs with
  | [] => true
  | q' :: qs => negb (q =? q') && negb (q =? q' + d) && negb (q' =? q + d) && safe q (d + 1) qs
  end.

(* Try columns [c..n-1] for the next queen; [sk] takes a solution and a
   failure continuation *)
Fixpoint place (fuel : nat) (n : int) (qs : list int) (row : int)
         (sk : list int -> (unit -> int) -> int) (fk : unit -> int) : int :=
  match fuel with
  | O => fk tt
  | S fuel =>
      if row =? n then sk qs fk
      else
        (fix try (cfuel : nat) (c : int) (fk : unit -> int) : int :=
           match cfuel with
           | O => fk tt
           | S cfuel =>
               if c =? n then fk tt
               else if safe c 1 qs
                    then place fuel n (c :: qs) (row + 1) sk (fun _ => try cfuel (c + 1) fk)
                    else try cfuel (c + 1) fk
           end) 20%nat 0 fk
  end.

Definition queens :=
  place 20 8 [] 0 (fun _ fk => 1 + fk tt) (fun _ => 0)
  + place 20 6 [] 0 (fun qs fk => sum qs + fk tt) (fun _ => 0).

(** * sort: merge sort parameterized by a comparator *)

Fixpoint merge (fuel : nat) (le : int -> int -> bool) (l1 l2 : list int) : list int :=
  match fuel with
  | O => l1 ++ l2
  | S fuel =>
      match l1, l2 with
      | [], l | l, [] => l
      | x :: l1', y :: l2' =>
          if le x y then x :: merge fuel le l1' l2 else y :: merge fuel le l1 l2'
      end
  end.

Fixpoint split (l : list int) : list int * list int :=
  match l with
  | x :: y :: l => let (a, b) := split l in (x :: a, y :: b)
  | _ => (l, [])
  end.

Fixpoint msort (fuel : nat) (le : int -> int -> bool) (l : list int) : list int :=
  match fuel with
  | O => l
  | S fuel =>
      match l with
      | [] | [_] => l
      | _ => let (a, b) := split l in merge fuel0 le (msort fuel le a) (msort fuel le b)
      end
  end.

Definition on (f : int -> int) (le : int -> int -> bool) : int -> int -> bool := fun x y => le (f x) (f y).
Definition rev_le (le : int -> int -> bool) : int -> int -> bool := fun x y => le y x.
Definition lex (le1 le2 : int -> int -> bool) : int -> int -> bool :=
  fun x y => if le1 x y then (if le1 y x then le2 x y else true) else false.

Fixpoint weigh (l : list int) (i : int) : int :=
  match l with [] => 0 | x :: l => i * x + weigh l (i + 1) end.

Definition sort :=
  let l := map (fun i => (i * 7919) mod 1009) (range 2000 0) in
  let les := [PrimInt63.leb; rev_le PrimInt63.leb; on (fun x => x mod 10) PrimInt63.leb; lex (on (fun x => x mod 7) PrimInt63.leb) (rev_le PrimInt63.leb)] in
  fold_left (fun acc le => acc + weigh (msort 30 le l) 1) les 0.

(** * pipeline: list combinators with many different function arguments *)

Fixpoint compose_all (fs : list (int -> int)) : int -> int :=
  match fs with
  | [] => fun x => x
  | f :: fs => let g := compose_all fs in fun x => g (f x)
  end.

Definition pipeline :=
  let fs := [fun x => x + 1; fun x => x * 3; fun x => x mod 1000; fun x => x - 2;
             fun x => x * x mod 997; fun x => x lxor 5] in
  let f := compose_all (fs ++ fs ++ fs) in
  loop 30 (fun acc =>
    let l := range 1000 acc in
    let l := map f l in
    let l := filter (fun x => x mod 3 =? 0) l in
    let l := map (fun x => x + acc) l in
    acc + fold_right (fun x y => x + 2 * y mod 100003) 0 l
        + fold_left (fun a x => if a <? x then x else a) l 0) 0.

(** * fmap: finite maps represented as functions *)

Definition fmap := int -> int.
Definition fupdate (m : fmap) (k v : int) : fmap := fun k' => if k =? k' then v else m k'.

Definition fmap_bench :=
  let m := fold_left (fun m i => fupdate m ((i * 37) mod 211) i) (range 400 0) (fun _ => 0) in
  fold_left (fun acc i => acc + m (i mod 251)) (range 2000 0) 0.

(* The expected results *)
Eval vm_compute in cps.
Eval vm_compute in parse.
Eval vm_compute in relabel_bench.
Eval vm_compute in compile.
Eval vm_compute in stream_bench.
Eval vm_compute in queens.
Eval vm_compute in sort.
Eval vm_compute in pipeline.
Eval vm_compute in fmap_bench.

CertiRocq Compile -O 1 -ext "_base" cps.
CertiRocq Compile -O 2 -ext "_web" cps.

CertiRocq Compile -O 1 -ext "_base" parse.
CertiRocq Compile -O 2 -ext "_web" parse.

CertiRocq Compile -O 1 -ext "_base" relabel_bench.
CertiRocq Compile -O 2 -ext "_web" relabel_bench.

CertiRocq Compile -O 1 -ext "_base" compile.
CertiRocq Compile -O 2 -ext "_web" compile.

CertiRocq Compile -O 1 -ext "_base" stream_bench.
CertiRocq Compile -O 2 -ext "_web" stream_bench.

CertiRocq Compile -O 1 -ext "_base" queens.
CertiRocq Compile -O 2 -ext "_web" queens.

CertiRocq Compile -O 1 -ext "_base" sort.
CertiRocq Compile -O 2 -ext "_web" sort.

CertiRocq Compile -O 1 -ext "_base" pipeline.
CertiRocq Compile -O 2 -ext "_web" pipeline.

CertiRocq Compile -O 1 -ext "_base" fmap_bench.
CertiRocq Compile -O 2 -ext "_web" fmap_bench.

