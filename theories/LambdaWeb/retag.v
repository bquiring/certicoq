(* Erasure for the compiler: function tags for internal webs.

   [erase] maps a web to its index, so an internal web [Internal p] becomes
   the λANF function tag [p].  The compiler's function environment does not
   know these tags, they may clash with existing tags, and functions of
   different arities may share a web.  [erase_rt] instead gives each pair of
   an internal web and an arity a fresh function tag, and records its arity
   in the function environment.  Exposed webs keep their λANF tag.

   A call and the functions it may call share a web, and a call only
   succeeds on a function of its arity, so the tags still agree wherever a
   call succeeds. *)

From Stdlib Require Import NArith.BinNat Lists.List.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import List_util.
From CertiRocq.LambdaANF Require term.
From CertiRocq.LambdaWeb Require Import syntax.

Import ListNotations.

Record rt_st : Type :=
  mk_rt { rt_map : M.t (list (nat * term.fun_tag));  (* tags of an internal web, by arity *)
          rt_next : term.fun_tag;                     (* the next fresh function tag *)
          rt_fenv : term.fun_env }.

Definition rt_tag (w : web) (n : nat) (s : rt_st) : term.fun_tag * rt_st :=
  match w with
  | Exposed t => (t, s)
  | Internal p =>
      let l := match M.get p (rt_map s) with Some l => l | None => [] end in
      match List.find (fun q => Nat.eqb (fst q) n) l with
      | Some (_, t) => (t, s)
      | None =>
          let t := rt_next s in
          (t, mk_rt (M.set p ((n, t) :: l) (rt_map s)) (Pos.succ t)
                    (M.set t (N.of_nat n, fromN 0%N n) (rt_fenv s)))
      end
  end.

Fixpoint erase_rt (e : exp) (s : rt_st) : term.exp * rt_st :=
  match e with
  | Econstr x w t ys e => let '(e, s) := erase_rt e s in (term.Econstr x t ys e, s)
  | Ecase x w cl =>
      let '(cl, s) :=
        (fix erase_br (cl : list (ctor_tag * exp)) (s : rt_st) :=
           match cl with
           | [] => ([], s)
           | (c, e) :: cl =>
               let '(e, s) := erase_rt e s in
               let '(cl, s) := erase_br cl s in
               ((c, e) :: cl, s)
           end) cl s in
      (term.Ecase x cl, s)
  | Eproj x w t n y e => let '(e, s) := erase_rt e s in (term.Eproj x t n y e, s)
  | Eletapp x f w ys e =>
      let '(t, s) := rt_tag w (length ys) s in
      let '(e, s) := erase_rt e s in
      (term.Eletapp x f t ys e, s)
  | Efun B e =>
      let '(B, s) := erase_rt_fds B s in
      let '(e, s) := erase_rt e s in
      (term.Efun B e, s)
  | Eapp f w ys => let '(t, s) := rt_tag w (length ys) s in (term.Eapp f t ys, s)
  | Eprim_val x p e => let '(e, s) := erase_rt e s in (term.Eprim_val x p e, s)
  | Eprim x p ys e => let '(e, s) := erase_rt e s in (term.Eprim x p ys e, s)
  | Ehalt x => (term.Ehalt x, s)
  end
with erase_rt_fds (B : fundefs) (s : rt_st) : term.fundefs * rt_st :=
  match B with
  | Fcons f w xs e B =>
      let '(t, s) := rt_tag w (length xs) s in
      let '(e, s) := erase_rt e s in
      let '(B, s) := erase_rt_fds B s in
      (term.Fcons f t xs e B, s)
  | Fnil => (term.Fnil, s)
  end.
