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
