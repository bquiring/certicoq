(* A concrete postcondition for transformations that remove and insert
   binding steps.

   Fuel is a natural number and the trace counts (non-call steps, call
   steps), as in LambdaANF/bounds.v.  [dead_bound L G] says that the source
   takes at most [G] more steps per call, plus [L], than the target, and
   that the target makes at least as many calls as the source.  It is the
   λweb counterpart of CertiRocq's [inline_bound L G]: it satisfies the
   λweb postcondition obligations, absorbs removed source binding steps
   (incrementing [L]) and inserted target binding steps, and gives an upper
   bound on the target's fuel in terms of the source's (divergence
   preservation). *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import algebra.
From CertiRocq.LambdaANF Require term bounds.
From CertiRocq.LambdaWeb Require Import syntax semantics exposed post.

Import ListNotations.

Open Scope alg_scope.
Open Scope nat_scope.

Existing Instance bounds.fuel_res.
Existing Instance bounds.trace_res.

Section Bound.

  Variable (cenv : term.ctor_env).

  Local Notation PostT := (@exposed.PostT nat (nat * nat)).

  Definition dead_bound (L G : nat) : PostT :=
    fun '(e1, rho1, c1, (t1, a1)) '(e2, rho2, c2, (t2, a2)) =>
      c1 <= c2 + G * a1 + L /\ a1 <= a2 /\ t2 + a2 = c2.

  Lemma one_w_fuel (e : exp) : (one_w e : nat) = 1.
  Proof. reflexivity. Qed.

  Definition is_call (e : exp) : bool :=
    match e with
    | Eapp _ _ _ | Eletapp _ _ _ _ _ | Eprim_val _ _ _ => true
    | _ => false
    end.

  Lemma one_w_trace (e : exp) :
    (one_w e : nat * nat) = if is_call e then (0, 1) else (1, 0).
  Proof. destruct e; reflexivity. Qed.

  Ltac simpl_bound :=
    unfold dead_bound, post_base' in *;
    repeat match goal with
           | [ p : (nat * nat)%type |- _ ] => destruct p
           end;
    unfold one_w, lt in *; cbn in *.

  Lemma dead_bound_properties L G :
    L <= G -> Post_properties cenv (dead_bound L G) (dead_bound L G) (dead_bound G G).
  Proof.
    intros HLG. constructor;
      [ .. | intros [[[? ?] ?] [? ?]] [[[? ?] ?] [? ?]]; simpl; lia ].
    all: repeat intro; simpl_bound; lia.
  Qed.

  Global Instance dead_bound_dead G :
    Post_dead cenv (fun n => dead_bound n G) (dead_bound G G) G.
  Proof.
    constructor.
    - intros n Hn. eapply dead_bound_properties; eauto.
    - intros n m Hnm Hm [[[? ?] ?] [? ?]] [[[? ?] ?] [? ?]]. simpl. lia.
    - intros n Hn e1 rho1 e1' rho1' e2 rho2 c1 [t1 a1] c2 [t2 a2] Hb.
      destruct e1; try contradiction; simpl_bound; lia.
  Qed.

  Lemma dead_bound_target_step L G : post_target_step (dead_bound L G).
  Proof.
    intros e1 rho1 c1 [t1 a1] e2 rho2 e2' rho2' c2 [t2 a2] Hb.
    destruct e2'; try contradiction; simpl_bound; lia.
  Qed.

  Lemma dead_bound_upper_bound L G : post_upper_bound (dead_bound L G).
  Proof.
    intros e1 rho1 e2 rho2. exists (fun c => (1 + G) * c + L).
    intros cin1 cin2 [t1 a1] [t2 a2] (H1 & H2 & H3).
    exists (cin2 - cin1). simpl. nia.
  Qed.

End Bound.
