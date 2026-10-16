(* Statistics on λweb programs, to report what the web optimizations do. *)

From Stdlib Require Import NArith.BinNat Lists.List.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require term.
From CertiRocq.LambdaWeb Require Import syntax.

Import ListNotations.

Record stats : Type :=
  mk_stats { n_fun : N;         (* function definitions *)
             n_fun_int : N;     (* ... with an internal web *)
             n_call : N;        (* calls *)
             n_call_int : N;    (* ... with an internal web *)
             n_con : N;         (* constructor allocations *)
             n_con_int : N;     (* ... with an internal web *)
             n_use : N;         (* projections and case analyses *)
             n_use_int : N;     (* ... with an internal web *)
             n_param : N;       (* parameters of functions *)
             n_arg : N;         (* arguments of calls *)
             n_bind : N }.      (* let-bound variables *)

Definition zero_stats : stats := mk_stats 0 0 0 0 0 0 0 0 0 0 0.

Definition intb (w : web) : N := if exposedb w then 0 else 1.

Definition add_fun (w : web) (np : nat) (s : stats) : stats :=
  let '(mk_stats f fi c ci k ki u ui p a b) := s in
  mk_stats (f + 1) (fi + intb w) c ci k ki u ui (p + N.of_nat np) a b.

Definition add_call (w : web) (na : nat) (bind : bool) (s : stats) : stats :=
  let '(mk_stats f fi c ci k ki u ui p a b) := s in
  mk_stats f fi (c + 1) (ci + intb w) k ki u ui p (a + N.of_nat na) (if bind then b + 1 else b).

Definition add_con (w : web) (s : stats) : stats :=
  let '(mk_stats f fi c ci k ki u ui p a b) := s in
  mk_stats f fi c ci (k + 1) (ki + intb w) u ui p a (b + 1).

Definition add_use (w : web) (bind : bool) (s : stats) : stats :=
  let '(mk_stats f fi c ci k ki u ui p a b) := s in
  mk_stats f fi c ci k ki (u + 1) (ui + intb w) p a (if bind then b + 1 else b).

Definition add_bind (s : stats) : stats :=
  let '(mk_stats f fi c ci k ki u ui p a b) := s in
  mk_stats f fi c ci k ki u ui p a (b + 1).

Fixpoint stats_exp (e : exp) (s : stats) : stats :=
  match e with
  | Econstr x w t ys e => stats_exp e (add_con w s)
  | Ecase x w cl =>
      (fix stats_br (cl : list (ctor_tag * exp)) (s : stats) :=
         match cl with
         | [] => s
         | (_, e) :: cl => stats_br cl (stats_exp e s)
         end) cl (add_use w false s)
  | Eproj x w t n y e => stats_exp e (add_use w true s)
  | Eletapp x f w ys e => stats_exp e (add_call w (length ys) true s)
  | Efun B e => stats_exp e (stats_fds B s)
  | Eapp f w ys => add_call w (length ys) false s
  | Eprim_val x p e => stats_exp e (add_bind s)
  | Eprim x p ys e => stats_exp e (add_bind s)
  | Ehalt x => s
  end
with stats_fds (B : fundefs) (s : stats) : stats :=
  match B with
  | Fcons f w xs e B => stats_fds B (stats_exp e (add_fun w (length xs) s))
  | Fnil => s
  end.

Definition stats_of (e : exp) : stats := stats_exp e zero_stats.

(** * Currying

    [(functions, functions whose body is a lambda returned at once,
      functions that return a lambda they define, calls whose result is
      called at once, calls whose result is bound)] *)

Definition cstats : Type := (N * N * N * N * N)%type.

(** Does [e] return a lambda it defines? [ls]: the lambdas in scope *)
Fixpoint ret_lam (ls : list var) (e : exp) : bool :=
  match e with
  | Econstr _ _ _ _ k | Eproj _ _ _ _ _ k | Eletapp _ _ _ _ k
  | Eprim_val _ _ k | Eprim _ _ _ k => ret_lam ls k
  | Ecase _ _ cl => existsb (fun p => ret_lam ls (snd p)) cl
  | Efun B k =>
      ret_lam ((fix names (B : fundefs) := match B with Fcons f _ _ _ B => f :: names B | Fnil => [] end) B ++ ls) k
  | Eapp _ _ _ => false
  | Ehalt x => existsb (Pos.eqb x) ls
  end.

Definition direct_lam (e : exp) : bool :=
  match e with Efun _ (Ehalt _) => true | _ => false end.

Definition calls_var (x : var) (e : exp) : bool :=
  match e with
  | Eapp f _ _ | Eletapp _ f _ _ _ => Pos.eqb f x
  | _ => false
  end.

Fixpoint curry_exp (e : exp) (s : cstats) : cstats :=
  match e with
  | Econstr _ _ _ _ k | Eproj _ _ _ _ _ k | Eprim_val _ _ k | Eprim _ _ _ k => curry_exp k s
  | Ecase _ _ cl =>
      (fix go (cl : list (ctor_tag * exp)) s :=
         match cl with
         | [] => s
         | (_, e) :: cl => go cl (curry_exp e s)
         end) cl s
  | Eletapp x _ _ _ k =>
      let '(f, d, r, i, l) := s in
      curry_exp k (f, d, r, if calls_var x k then i + 1 else i, l + 1)%N
  | Efun B k => curry_exp k (curry_fds B s)
  | Eapp _ _ _ | Ehalt _ => s
  end
with curry_fds (B : fundefs) (s : cstats) : cstats :=
  match B with
  | Fcons _ _ _ e B =>
      let '(f, d, r, i, l) := s in
      let s := (f + 1, if direct_lam e then d + 1 else d, if ret_lam [] e then r + 1 else r, i, l)%N in
      curry_fds B (curry_exp e s)
  | Fnil => s
  end.

Definition curry_of (e : exp) : cstats := curry_exp e (0, 0, 0, 0, 0)%N.
