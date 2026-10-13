(* Exposed values do not depend on the transformation-specific relation
   (Theorem 5.1 of the paper), and its consequence for top-level terms
   (Corollary 5.2).

   The λweb relation is the instantiation of the parameterized relation
   with the empty relation for internal closures. *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics algebra.
From CertiRocq.LambdaANF Require term term_util.
From CertiRocq.LambdaWeb Require Import syntax semantics exposed post.

Import ListNotations.

Open Scope alg_scope.

Section Indep.

  Variable (cenv : term.ctor_env).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Local Notation PostT := (@exposed.PostT fuel trace).
  Local Notation PostGT := (@exposed.PostGT fuel trace).
  Local Notation VTransT := (@exposed.VTransT fuel trace).

  (** The λweb relation: no internal closure is related to anything. *)
  Definition VT_web : VTransT := fun _ _ _ _ _ => False.

  Global Instance VTransProps_web : VTransProps VT_web.
  Proof. constructor; unfold VT_web; tauto. Qed.

  Lemma E'_exposed_ext (V1 V2 : nat -> val -> val -> Prop) P k p1 p2 :
    (forall j, j <= k -> forall v1 v2, exposed_val v1 -> V1 j v1 v2 <-> V2 j v1 v2) ->
    E' cenv V1 P true k p1 p2 -> E' cenv V2 P true k p1 p2.
  Proof.
    destruct p1 as [e1 rho1], p2 as [e2 rho2]. simpl.
    intros Hext HE r1 cin cout Hleq Hstep.
    edestruct HE as (r2 & cin' & cout' & Hstep' & HP & HR); eauto.
    do 3 eexists; split; [ eassumption | split; [ eassumption |] ].
    destruct r1, r2; simpl in *; eauto.
    eapply Hext; eauto. lia. eapply bstep_fuel_exposed_val; eauto.
  Qed.

  Lemma V_fun_exposed_indep (VT1 VT2 : VTransT) PG k rho1 B1 f1 v2 :
    exposed_val (Vfun rho1 B1 f1) ->
    (forall j, j < k -> forall v1 v2, exposed_val v1 -> V cenv VT1 PG j v1 v2 <-> V cenv VT2 PG j v1 v2) ->
    V_fun cenv PG (V cenv VT1 PG) k (Vfun rho1 B1 f1) v2 ->
    V_fun cenv PG (V cenv VT2 PG) k (Vfun rho1 B1 f1) v2.
  Proof.
    intros Hexp IH. rewrite exposed_val_Vfun in Hexp. destruct Hexp as (w0 & xs0 & e0 & Hfind & Hw0).
    destruct v2; cbn -[E']; try easy.
    intros Hfn vs1 vs2 j w xs1 e1 rho1' Hlen Hfind' Hset.
    edestruct (Hfn vs1 vs2 j w xs1 e1 rho1' Hlen Hfind' Hset) as (xs2 & e2 & rho2' & Hfind2 & Hset2 & Hbody).
    rewrite Hfind in Hfind'. inv Hfind'.
    do 3 eexists. split; [ eassumption | split; [ eassumption |] ].
    intros Hlt Hexp Hall. rewrite Hw0 in *.
    specialize (Hexp eq_refl).
    eapply E'_exposed_ext; [| eapply Hbody; eauto ].
    - intros. eapply IH; eauto. lia.
    - clear -IH Hlt Hexp Hall. induction Hall; inv Hexp; constructor; eauto.
      eapply IH; eauto.
  Qed.

  Section TwoVT.

    Context (VT1 VT2 : VTransT) {HVT1 : VTransProps VT1} {HVT2 : VTransProps VT2}.


    (** Theorem 5.1 *)
    Theorem V_exposed_indep PG k :
      forall v1 v2, exposed_val v1 -> (V cenv VT1 PG k v1 v2 <-> V cenv VT2 PG k v1 v2).
    Proof.
      induction k as [k IHk] using lt_wf_rec.
      assert (IH : forall j, j < k -> forall v1 v2, exposed_val v1 ->
                                            V cenv VT1 PG j v1 v2 <-> V cenv VT2 PG j v1 v2)
        by (intros; eapply IHk; eauto).
      assert (IH' : forall j, j < k -> forall v1 v2, exposed_val v1 ->
                                             V cenv VT2 PG j v1 v2 <-> V cenv VT1 PG j v1 v2)
        by (intros; symmetry; eapply IHk; eauto).
      intros v1. induction v1 using val_ind_Forall; intros v2 Hexp;
        rewrite (V_eq cenv VT1 PG k), (V_eq cenv VT2 PG k); unfold V_.
      - rewrite exposed_val_Vconstr in Hexp. destruct Hexp as [Hw Hvs].
        destruct v2; try tauto.
        assert (Hiff : Forall2 (V cenv VT1 PG k) vs l <-> Forall2 (V cenv VT2 PG k) vs l).
        { clear -H Hvs. revert l. induction H; intros l2; inv Hvs; split; intros Hall; inv Hall;
            constructor; try (eapply H; eauto); eapply IHForall; eauto. }
        rewrite Hiff. reflexivity.
      - pose proof Hexp as Hexp'.
        rewrite exposed_val_Vfun in Hexp'. destruct Hexp' as (w & xs & e & Hfind & Hw).
        unfold fun_web. rewrite Hfind, Hw.
        split; intros (Hwf1 & Hwf2 & Hiff & Hfun); repeat (split; [ eassumption |]);
          [ eapply (V_fun_exposed_indep VT1 VT2) | eapply (V_fun_exposed_indep VT2 VT1) ]; eauto.
      - reflexivity.
      - reflexivity.
    Qed.

    Corollary R_exposed_indep PG k r1 r2 :
      exposed_res r1 -> (R cenv VT1 PG k r1 r2 <-> R cenv VT2 PG k r1 r2).
    Proof. destruct r1, r2; simpl; try tauto. eapply V_exposed_indep. Qed.

    Corollary E_exposed_indep PG P k p1 p2 :
      E cenv VT1 PG P true k p1 p2 -> E cenv VT2 PG P true k p1 p2.
    Proof.
      eapply E'_exposed_ext. intros. eapply V_exposed_indep; eauto.
    Qed.

  End TwoVT.

  (** * Top-level relations *)

  (** Imported values are exposed. *)
  Definition G_top (VT : VTransT) (PG : PostGT) (k : nat) (S : Ensemble var) (rho1 rho2 : env) : Prop :=
    G cenv VT PG k S rho1 rho2 /\
    (forall x v, S x -> M.get x rho1 = Some v -> exposed_val v).

  (** Top-level expression relation: in related exposed environments, the
      programs produce related (exposed) results. *)
  Definition E_top (VT : VTransT) (P : PostT) (PG : PostGT) (e1 e2 : exp) : Prop :=
    forall k rho1 rho2,
      G_top VT PG k (occurs_free e1) rho1 rho2 ->
      term_util.binding_in_map (occurs_free e1) rho1 ->
      E cenv VT PG P true k (e1, rho1) (e2, rho2).

  Definition E_web := E_top VT_web.

  Lemma G_top_exposed_indep VT1 VT2 {HVT1 : VTransProps VT1} {HVT2 : VTransProps VT2}
        PG k S rho1 rho2 :
    G_top VT1 PG k S rho1 rho2 -> G_top VT2 PG k S rho1 rho2.
  Proof.
    intros [(Hwf1 & Hwf2 & HG) Hexp]. split; [ split; [| split ] |]; eauto.
    intros x Hx v1 Hget. edestruct HG as (v2 & Hget2 & Hv); eauto.
    eexists; split; eauto. eapply (proj1 (V_exposed_indep VT1 VT2 PG k v1 v2 (Hexp x v1 Hx Hget))); eauto.
  Qed.

  (** Corollary 5.2: every instantiation implies the λweb relation. *)
  Corollary E_top_E_web VT {HVT : VTransProps VT} P PG e1 e2 :
    E_top VT P PG e1 e2 -> E_web P PG e1 e2.
  Proof.
    intros Htop k rho1 rho2 HG Hbind.
    eapply (E_exposed_indep VT VT_web). eapply Htop; eauto.
    eapply (G_top_exposed_indep VT_web VT); eauto.
  Qed.

End Indep.
