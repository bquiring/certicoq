(* Removing and inserting binding steps.

   Dead-binding elimination removes source evaluation steps ([Econstr],
   [Eproj] and [Efun] bindings whose variables are dead in the target);
   constant propagation inserts target steps (bindings of constants).  The
   lemmas below relate an expression to one with a binding step on one side
   only, for any transformation-specific relation [VT]; the postconditions
   absorb the step through [post_source_step] and [post_target_step]
   (post.v). *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics algebra.
From CertiRocq.LambdaANF Require term term_util.
From CertiRocq.LambdaWeb Require Import syntax semantics exposed post compat.

Import ListNotations.

Open Scope alg_scope.

Section Dead.

  Variable (cenv : term.ctor_env).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Local Notation PostT := (@exposed.PostT fuel trace).
  Local Notation PostGT := (@exposed.PostGT fuel trace).
  Local Notation VTransT := (@exposed.VTransT fuel trace).

  Context (VT : VTransT) {HVT : VTransProps VT} (PG : PostGT).

  Notation V := (V cenv VT PG).
  Notation E := (E cenv VT PG).
  Notation G := (G cenv VT PG).

  Ltac fuel_arith :=
    repeat match goal with
           | [ H : context [ to_nat (_ <+> _) ] |- _ ] => rewrite to_nat_add in H
           | [ |- context [ to_nat (_ <+> _) ] ] => rewrite to_nat_add
           | [ H : context [ to_nat (one_w _) ] |- _ ] => rewrite to_nat_one_w in H
           | [ |- context [ to_nat (one_w _) ] ] => rewrite to_nat_one_w
           end; lia.

  (** * Source-only steps *)

  Lemma E_source_step (P1 P2 : PostT) ex k e1 rho1 e2 rho2
        (He1 : binding_step e1)
        (Hsrc : post_source_step P1 P2)
        (HOOT : post_OOT' e1 rho1 e2 rho2 P2) :
    (forall cin r cout,
        bstep cenv ex rho1 e1 cin r cout ->
        exists e1' rho1', bstep_fuel cenv ex rho1' e1' cin r cout /\
                          E P1 ex k (e1', rho1') (e2, rho2)) ->
    E P2 ex k (e1, rho1) (e2, rho2).
  Proof.
    intros Hstep r1 cin cout Hleq Hs. inv Hs.
    - exists OOT, cin, <0>. split; [ constructor; rewrite (one_w_eq e2 e1); eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - edestruct Hstep as (e1' & rho1' & Hs' & HE); eauto.
      edestruct HE as (r2 & cin' & cout' & Hs2 & HP & HR); [| eassumption |]; [ fuel_arith |].
      do 3 eexists. split; [ eassumption | split; [ eapply Hsrc; eauto |] ].
      eapply (R_mono cenv VT); eauto. fuel_arith.
  Qed.

  Lemma E_dead_constr (P1 P2 : PostT) ex k x w t ys e1 rho1 e2 rho2
        (Hsrc : post_source_step P1 P2)
        (HOOT : post_OOT' (Econstr x w t ys e1) rho1 e2 rho2 P2) :
    wf_env rho1 ->
    (forall vs, get_list ys rho1 = Some vs -> wf_val (Vconstr w t vs) ->
                E P1 ex k (e1, M.set x (Vconstr w t vs) rho1) (e2, rho2)) ->
    E P2 ex k (Econstr x w t ys e1, rho1) (e2, rho2).
  Proof.
    intros Hwf He. eapply E_source_step; eauto; [ exact I |].
    intros cin r cout Hs. inv Hs. do 2 eexists. split; [ eassumption |].
    eapply He; eauto. constructor; eauto. eapply wf_env_get_list; eauto.
  Qed.

  Lemma E_dead_proj (P1 P2 : PostT) ex k x w t n y e1 rho1 e2 rho2
        (Hsrc : post_source_step P1 P2)
        (HOOT : post_OOT' (Eproj x w t n y e1) rho1 e2 rho2 P2) :
    wf_env rho1 ->
    (forall v, wf_val v -> E P1 ex k (e1, M.set x v rho1) (e2, rho2)) ->
    E P2 ex k (Eproj x w t n y e1, rho1) (e2, rho2).
  Proof.
    intros Hwf He. eapply E_source_step; eauto; [ exact I |].
    intros cin r cout Hs. inv Hs. do 2 eexists. split; [ eassumption |].
    eapply He.
    match goal with
    | [ Hg : M.get y rho1 = Some _, Hn : nthN _ _ = Some _ |- _ ] =>
        pose proof (wf_env_get _ _ _ Hwf Hg) as Hc; inv Hc; eapply nthN_Forall; eauto
    end.
  Qed.

  Lemma E_dead_fun (P1 P2 : PostT) ex k B e1 rho1 e2 rho2
        (Hsrc : post_source_step P1 P2)
        (HOOT : post_OOT' (Efun B e1) rho1 e2 rho2 P2) :
    E P1 ex k (e1, def_funs B B rho1 rho1) (e2, rho2) ->
    E P2 ex k (Efun B e1, rho1) (e2, rho2).
  Proof.
    intros He. eapply E_source_step; eauto; [ exact I |].
    intros cin r cout Hs. inv Hs. do 2 eexists. split; eassumption.
  Qed.

  (** * Target-only steps *)

  Lemma E_add_constr (P : PostT) ex k p1 x w t e2 rho2
        (Htgt : post_target_step P) :
    E P ex k p1 (e2, M.set x (Vconstr w t []) rho2) ->
    E P ex k p1 (Econstr x w t [] e2, rho2).
  Proof.
    destruct p1 as [e1 rho1]. intros HE r1 cin cout Hleq Hs.
    edestruct HE as (r2 & cin' & cout' & Hs2 & HP & HR); eauto.
    do 3 eexists. split; [| split; [ eapply Htgt; [ exact I | eassumption ] | eassumption ] ].
    econstructor 2; [ econstructor; eauto; reflexivity |].
    intros Hex; subst. eapply bstep_fuel_exposed; eauto.
  Qed.

  (** * Environments *)

  Lemma G_set_r_not_in k S rho1 rho2 x v :
    G k S rho1 rho2 -> wf_val v -> ~ S x -> G k S rho1 (M.set x v rho2).
  Proof.
    intros (Hwf1 & Hwf2 & HG) Hv Hnin. split; [| split ]; eauto using wf_env_set.
    intros y Hy v1 Hget. edestruct HG as (v2 & Hget2 & Hv2); eauto.
    exists v2. rewrite M.gso; [ split; eauto |]. intros Hc; subst; eauto.
  Qed.

  Lemma G_def_funs_l_not_in k S rho1 rho2 B rhoc :
    G k S rho1 rho2 -> wf_env rhoc -> Disjoint _ (name_in_fundefs B) S ->
    G k S (def_funs B B rhoc rho1) rho2.
  Proof.
    intros (Hwf1 & Hwf2 & HG) Hwfc Hdis.
    split; [ eapply wf_env_def_funs; eauto | split; [ eassumption |] ].
    intros y Hy v1 Hget. rewrite def_funs_neq in Hget; [ eapply HG; eauto |].
    intros Hc. eapply Hdis; constructor; eauto.
  Qed.

End Dead.
