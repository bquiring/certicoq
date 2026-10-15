(* Erasure for the compiler: function tags for internal webs.

   [erase] maps a web to its index, so an internal web [Internal p] becomes
   the λANF function tag [p].  The compiler's function environment does not
   know these tags, they may clash with existing tags, and functions of
   different arities may share a web.  The compiler instead erases with
   [tagf_glob], which gives each pair of an internal web and an arity its
   own tag, far above the tags λANF programs use, and records its arity in
   the function environment ([fenv_of]).  Exposed webs keep their λANF tag.

   A call and the functions it may call share a web, and a call only
   succeeds on a function of its arity, so the tags still agree wherever a
   call succeeds.  The tag function does not depend on the program, so
   separately compiled units erase with the same one, which linking needs.

   [fenv_of] checks that the tags it adds do not already have a different
   arity in the function environment; the compiler keeps its input
   otherwise. *)

From Stdlib Require Import NArith.BinNat Lists.List.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import List_util.
From CertiRocq.LambdaANF Require term.
From CertiRocq.LambdaWeb Require Import syntax.

Import ListNotations.

(** The tag of an internal web [p] at arity [n]: [n] trailing zeros after
    the odd number [2 (p + 2^20) + 1] *)
Fixpoint shift_tag (n : nat) (t : positive) : positive :=
  match n with
  | O => t
  | S n => xO (shift_tag n t)
  end.

Definition int_tag (p : positive) (n : nat) : term.fun_tag := shift_tag n (xI (p + 1048576)).

Definition tagf_glob (w : web) (n : nat) : term.fun_tag :=
  match w with
  | Exposed t => t
  | Internal p => int_tag p n
  end.

Lemma tagf_glob_exposed t n : tagf_glob (Exposed t) n = t.
Proof. reflexivity. Qed.

(** * The function environment *)

Definition fun_info (n : nat) : N * list N := (N.of_nat n, fromN 0 n).

Fixpoint nlist_eqb (l1 l2 : list N) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: l1, y :: l2 => N.eqb x y && nlist_eqb l1 l2
  | _, _ => false
  end.

Definition info_eqb (i1 i2 : N * list N) : bool :=
  N.eqb (fst i1) (fst i2) && nlist_eqb (snd i1) (snd i2).

(** Record the tag of a web at an arity; [false] if the tag is known with
    another arity *)
Definition add_tag (w : web) (n : nat) (acc : term.fun_env * bool * positive) : term.fun_env * bool * positive :=
  match w with
  | Exposed _ => acc
  | Internal p =>
      let '(fenv, ok, mx) := acc in
      let t := int_tag p n in
      match M.get t fenv with
      | Some i => (fenv, ok && info_eqb i (fun_info n), Pos.max mx t)
      | None => (M.set t (fun_info n) fenv, ok, Pos.max mx t)
      end
  end.

(** The function environment extended with the tags of the internal webs of
    a program, whether it is consistent, and the largest tag *)
Fixpoint fenv_of (e : exp) (acc : term.fun_env * bool * positive) : term.fun_env * bool * positive :=
  match e with
  | Econstr _ _ _ _ e | Eproj _ _ _ _ _ e | Eprim_val _ _ e | Eprim _ _ _ e => fenv_of e acc
  | Ecase _ _ cl =>
      (fix fenv_br (cl : list (ctor_tag * exp)) acc :=
         match cl with
         | [] => acc
         | (_, e) :: cl => fenv_br cl (fenv_of e acc)
         end) cl acc
  | Eletapp _ _ w ys e => fenv_of e (add_tag w (length ys) acc)
  | Efun B e => fenv_of e (fenv_of_fds B acc)
  | Eapp _ w ys => add_tag w (length ys) acc
  | Ehalt _ => acc
  end
with fenv_of_fds (B : fundefs) (acc : term.fun_env * bool * positive) : term.fun_env * bool * positive :=
  match B with
  | Fcons _ w xs e B => fenv_of_fds B (fenv_of e (add_tag w (length xs) acc))
  | Fnil => acc
  end.
