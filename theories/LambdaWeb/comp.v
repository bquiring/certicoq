(* Compositionality of the λweb relation (Section 7.3 of the paper), in
   the style of LambdaANF/rel_comp.v: the transitive closure of the
   top-level λweb relation implies behavioral refinement (termination and
   divergence preservation, Lemma 7.5) and is compatible with linking
   (Lemma 7.6). *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations Classes.RelationClasses.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics algebra set_util.
From CertiRocq.LambdaANF Require term term_util identifiers rel_comp.
From CertiRocq.LambdaWeb Require Import syntax semantics exposed post compat indep refl.

Import ListNotations.

Open Scope alg_scope.

Section Types.

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Local Notation PostT := (@exposed.PostT fuel trace).
  Local Notation PostGT := (@exposed.PostGT fuel trace).
  Local Notation VTransT := (@exposed.VTransT fuel trace).

  Definition post_property := PostT -> PostGT -> Prop.

  (** Transitive closure of a family of relations indexed by
      postconditions, as in LambdaANF/rel_comp.v *)
  Section Compose.

    Context {A : Type} (wf_pres : A -> A -> Prop) (post_prop : post_property).

    Inductive R_n (R : PostT -> PostGT -> A -> A -> Prop) : nat -> A -> A -> Prop :=
    | One :
        forall (P : PostT) (PG : PostGT) (c1 c2 : A),
          R P PG c1 c2 ->
          wf_pres c1 c2 ->
          post_prop P PG ->
          R_n R 1%nat c1 c2
    | More :
        forall (n m : nat) (c1 c2 c' : A),
          R_n R n c1 c' ->
          R_n R m c' c2 ->
          R_n R (n + m) c1 c2.

    Lemma R_n_wf_pres {Htr : Transitive wf_pres} R n c1 c2 : R_n R n c1 c2 -> wf_pres c1 c2.
    Proof. intros H; induction H; eauto. Qed.

    Lemma R_n_trans R n m c1 c2 c3 : R_n R n c1 c2 -> R_n R m c2 c3 -> R_n R (n + m) c1 c3.
    Proof. intros. eapply More; eauto. Qed.

  End Compose.

  Definition compose_rel {A B C} (R1 : A -> B -> Prop) (R2 : B -> C -> Prop) (a : A) (c : C) : Prop :=
    exists b, R1 a b /\ R2 b c.

  Definition preserves_fv (e1 e2 : exp) := occurs_free e2 \subset occurs_free e1.

  Global Instance preserves_fv_trans : Transitive preserves_fv.
  Proof. intros e1 e2 e3 H1 H2. unfold preserves_fv in *. eapply Included_trans; eauto. Qed.

  Lemma closed_preserves_fv e1 e2 : closed_exp e1 -> preserves_fv e1 e2 -> closed_exp e2.
  Proof.
    intros Hc Hp. split; [| sets ]. eapply Included_trans; [ eapply Hp | eapply Hc ].
  Qed.

  (** * Value refinement for λweb *)

  Fixpoint value_ref' (v1 v2 : val) : Prop :=
    let fix Forall2_aux vs1 vs2 :=
      match vs1, vs2 with
      | [], [] => True
      | v1 :: vs1, v2 :: vs2 => value_ref' v1 v2 /\ Forall2_aux vs1 vs2
      | _, _ => False
      end in
    match v1, v2 with
    | Vconstr w1 c1 vs1, Vconstr w2 c2 vs2 => w1 = w2 /\ c1 = c2 /\ Forall2_aux vs1 vs2
    | Vfun _ _ _, Vfun _ _ _ => True
    | Vint i1, Vint i2 => i1 = i2
    | Vprim p1, Vprim p2 => p1 = p2
    | _, _ => False
    end.

  Definition value_ref (v1 v2 : val) : Prop :=
    match v1, v2 with
    | Vconstr w1 c1 vs1, Vconstr w2 c2 vs2 => w1 = w2 /\ c1 = c2 /\ Forall2 value_ref' vs1 vs2
    | Vfun _ _ _, Vfun _ _ _ => True
    | Vint i1, Vint i2 => i1 = i2
    | Vprim p1, Vprim p2 => p1 = p2
    | _, _ => False
    end.

  Lemma value_ref_eq v1 v2 : value_ref' v1 v2 <-> value_ref v1 v2.
  Proof.
    destruct v1, v2; simpl; try reflexivity.
    split; intros (Hw & Hc & Hall); (split; [ exact Hw | split; [ exact Hc |] ]).
    - revert l0 Hall. induction l; intros l0 Hall; destruct l0; try contradiction.
      + constructor.
      + destruct Hall as [Hv Hall]. constructor; eauto.
    - induction Hall; simpl; [ exact I | split; assumption ].
  Qed.

  Global Instance value_ref_trans : Transitive value_ref.
  Proof.
    intros v1. induction v1 using val_ind_Forall; intros v2 v3 H1 H2;
      destruct v2, v3; simpl in *; try contradiction; destructAll; eauto.
    split; eauto. split; eauto.
    match goal with
    | [ Ha : Forall2 value_ref' vs ?l, Hb : Forall2 value_ref' ?l ?l' |- _ ] =>
        revert l l' Ha Hb
    end.
    induction H; intros l1 l2 Hall1 Hall2; inv Hall1; inv Hall2; constructor; eauto.
    rewrite value_ref_eq in *. eauto.
  Qed.

  (** Termination and divergence refinement for closed λweb programs *)

  Definition emp : env := M.empty val.

  Definition refines (cenv : term.ctor_env) (vref : val -> val -> Prop) (e1 e2 : exp) :=
    (forall v1 c1 t1,
        bstep_fuel cenv true emp e1 c1 (Res v1) t1 ->
        exists v2 c2 t2, bstep_fuel cenv true emp e2 c2 (Res v2) t2 /\ vref v1 v2) /\
    (diverge cenv true emp e1 -> diverge cenv true emp e2).

  Lemma refines_trans cenv e1 e2 e3 :
    refines cenv value_ref e1 e2 -> refines cenv value_ref e2 e3 -> refines cenv value_ref e1 e3.
  Proof.
    intros [Ht1 Hd1] [Ht2 Hd2]. split; eauto.
    intros v1 c1 t1 Hs. edestruct Ht1 as (v2 & c2 & t2 & Hs2 & Hr2); eauto.
    edestruct Ht2 as (v3 & c3 & t3 & Hs3 & Hr3); eauto.
    do 3 eexists; split; eauto. etransitivity; eauto.
  Qed.

  Section Adequacy.

    Variable (cenv : term.ctor_env).

    Lemma V_web_value_ref PG k v1 v2 : V cenv VT_web PG k v1 v2 -> value_ref v1 v2.
    Proof.
      revert v2. induction v1 using val_ind_Forall; intros v2 Hv;
        rewrite (V_eq cenv VT_web) in Hv; unfold V_ in Hv; destructAll.
      - destruct v2; try contradiction. destructAll. simpl. repeat split; eauto.
        clear H0 H1 H2. revert l H5. induction H; intros l2 Hall; inv Hall; constructor; eauto.
        rewrite value_ref_eq. eauto.
      - destruct (fun_web B f) as [w |]; [ destruct (exposedb w) |]; try contradiction.
        eapply V_fun_Vfun_inv in H2. destructAll. simpl. auto.
      - destruct v2; try contradiction. simpl; eauto.
      - destruct v2; try contradiction. simpl; eauto.
    Qed.

    Lemma G_top_empty VT {HVT : VTransProps VT} PG k S rho1 rho2 :
      S <--> Empty_set _ -> wf_env rho1 -> wf_env rho2 -> G_top cenv VT PG k S rho1 rho2.
    Proof.
      intros HS Hwf1 Hwf2. split.
      - eapply (G_antimon cenv VT); [ eapply (G_empty cenv VT); eauto | eapply HS ].
      - intros x v Hx. eapply HS in Hx. inv Hx.
    Qed.

    Lemma E_web_refines P PG (HP : post_upper_bound P) e1 e2 :
      closed_exp e1 -> E_web cenv P PG e1 e2 -> refines cenv value_ref e1 e2.
    Proof.
      intros Hc Hrel. split.
      - intros v1 c1 t1 Hs.
        edestruct (Hrel (to_nat c1) emp emp) as (r2 & c2 & t2 & Hs2 & Hpost & HR);
          [ eapply G_top_empty; eauto using wf_env_empty
          | intros x Hx; eapply Hc in Hx; inv Hx | | eassumption | ].
        + reflexivity.
        + destruct r2 as [| v2]; try contradiction.
          do 3 eexists. split; eauto. eapply V_web_value_ref; eauto.
      - intros Hdiv c2.
        destruct (HP e1 emp e2 emp) as [f Hfn].
        destruct (Hdiv (f c2)) as [t1 Hs].
        edestruct (Hrel (to_nat (f c2)) emp emp) as (r2 & c2' & t2 & Hs2 & Hpost & HR);
          [ eapply G_top_empty; eauto using wf_env_empty
          | intros x Hx; eapply Hc in Hx; inv Hx | reflexivity | eassumption | ].
        destruct r2; try contradiction.
        edestruct Hfn as [c Heq]; eauto. subst.
        edestruct bstep_fuel_OOT_monotonic as (t2' & c' & Hs2' & _); eauto.
    Qed.

    Context (wf_pres : exp -> exp -> Prop) (post_prop : post_property)
            (Hwf : forall e1 e2, wf_pres e1 e2 -> preserves_fv e1 e2)
            (Hpost : forall P PG, post_prop P PG -> post_upper_bound P).

    Definition web_exp_n n := R_n wf_pres post_prop (fun P PG e1 e2 => E_web cenv P PG e1 e2) n.

    Lemma R_n_preserves_fv R n e1 e2 : R_n wf_pres post_prop R n e1 e2 -> preserves_fv e1 e2.
    Proof. intros H; induction H; eauto. eapply preserves_fv_trans; eauto. Qed.

    (** Lemma 7.5: adequacy for λweb *)
    Theorem web_exp_n_refines n e1 e2 :
      closed_exp e1 -> web_exp_n n e1 e2 -> refines cenv value_ref e1 e2.
    Proof.
      intros Hc Hrel. revert Hc. induction Hrel; intros Hc.
      - eapply E_web_refines; eauto.
      - eapply refines_trans; [ eapply IHHrel1; eauto | eapply IHHrel2 ].
        eapply closed_preserves_fv; eauto. eapply R_n_preserves_fv; eauto.
    Qed.

  End Adequacy.

  (** * Linking *)

  Section Linking.

    Variable (cenv : term.ctor_env).

    (** The web of linking thunks: it is exposed, since it is the interface
        between separately compiled units.  It is the function tag λANF uses
        for linking. *)
    Variable (lft : web).
    Hypothesis (Hlft : exposedb lft = true).

    Definition link_var (x : var) (e1 e2 : exp) : var :=
      (identifiers.max_var (erase e1) (identifiers.max_var (erase e2) x) + 1)%positive.

    Definition link_w (x : var) (e1 e2 : exp) : exp :=
      link (link_var x e1 e2) lft x e1 e2.

    (** Linking erases to λANF linking. *)
    Lemma erase_link_w x e1 e2 :
      erase (link_w x e1 e2) = CertiRocq.LambdaANF.rel_comp.link lft x (erase e1) (erase e2).
    Proof. reflexivity. Qed.

    Lemma link_closed x e1 e2 :
      closed_exp e1 ->
      occurs_free e2 \subset [set x] ->
      closed_exp (link_w x e1 e2).
    Proof.
      intros Hc Hs. unfold closed_exp, occurs_free. rewrite erase_link_w.
      exact (CertiRocq.LambdaANF.rel_comp.link_closed lft x (erase e1) (erase e2) Hc Hs).
    Qed.

    Context (P : PostT) (PG : PostGT) (Hpr : Post_properties cenv P P PG).

    Lemma E_web_preserves_linking x e1 e2 e1' e2' :
      closed_exp e1 ->
      E_web cenv P PG e1 e2 ->
      E_web cenv P PG e1' e2' ->
      occurs_free e1' \subset [set x] ->
      E_web cenv P PG (link_w x e1 e1') (link_w x e2 e2').
    Proof.
      intros Hc Hlib Hcl Hfv k rho1 rho2 [HG Hexp] Hbind. inv Hpr.
      unfold link_w, link.
      eapply (E_fun_compat cenv VT_web); eauto.
      eapply (E_letapp_compat cenv VT_web); eauto.
      - eapply (var_rel_exposed_fun cenv VT_web); eauto.
        intros v1 Hget. simpl in Hget. rewrite M.gss in Hget. inv Hget.
        eexists. simpl. rewrite M.gss. split; [ reflexivity |].
        eapply (V_Vfun_exposed cenv VT_web); try (simpl; rewrite peq_true; reflexivity); eauto;
          try now apply HG.
        eapply (V_fun_def cenv VT_web); try (simpl; rewrite peq_true; reflexivity); eauto.
        intros j vs1 vs2 rho1' rho2' Hlt Hexpv Hvs Hs1 Hs2.
        destruct vs1; [| simpl in Hs1; congruence ]. destruct vs2; [| simpl in Hs2; congruence ].
        inv Hs1. inv Hs2. rewrite Hlft.
        eapply (E_post_mono cenv VT_web); [ eassumption |].
        eapply Hlib.
        + eapply (G_top_empty cenv VT_web); [ eapply Hc | |];
            (first [ eapply wf_env_def_funs; apply HG
                   | eapply wf_env_set; [ apply HG | constructor; apply HG ] ]).
        + intros z Hz. eapply Hc in Hz. inv Hz.
      - intros m v1 v2 Hlt Hexpv Hv.
        eapply Hcl.
        + split.
          * eapply (G_antimon cenv VT_web); [| eassumption ].
            eapply (G_set cenv VT_web); eauto. split; [| split ].
            -- first [ eapply wf_env_def_funs; apply HG
                     | eapply wf_env_set; [ apply HG | constructor; apply HG ] ].
            -- first [ eapply wf_env_def_funs; apply HG
                     | eapply wf_env_set; [ apply HG | constructor; apply HG ] ].
            -- intros z [Hz Hn]. contradiction.
          * intros z v Hz Hget. eapply Hfv in Hz. inv Hz. rewrite M.gss in Hget. inv Hget. eauto.
        + intros z Hz. eapply Hfv in Hz. inv Hz. eexists. rewrite M.gss. reflexivity.
    Qed.

  End Linking.

  Section LinkingComp.

    Variable (cenv : term.ctor_env) (lft : web).
    Hypothesis (Hlft : exposedb lft = true).

    Context (post_prop : post_property)
            (Hpr : forall P PG, post_prop P PG -> Post_properties cenv P P PG).

    Notation web_exp_n := (web_exp_n cenv preserves_fv post_prop).

    Lemma web_exp_n_preserves_linking_src_l x n e1 e2 e1' :
      web_exp_n n e1 e2 ->
      closed_exp e1 ->
      occurs_free e1' \subset [set x] ->
      web_exp_n n (link_w lft x e1 e1') (link_w lft x e2 e1').
    Proof.
      intros Hrel. revert e1'. induction Hrel; intros e1' Hc Hfv.
      - econstructor; [| | eassumption ].
        + eapply E_web_preserves_linking; eauto. eapply E_web_refl; eauto.
        + intros z Hz. exfalso.
          assert (Hc2 : closed_exp c2) by (eapply closed_preserves_fv; eauto).
          destruct (link_closed lft x c2 e1' Hc2 Hfv) as [Hl _]. eapply Hl in Hz. inv Hz.
      - econstructor; [ eapply IHHrel1; eauto | eapply IHHrel2; eauto ].
        eapply closed_preserves_fv; eauto. eapply R_n_preserves_fv; eauto.
    Qed.

    Lemma web_exp_n_preserves_linking_src_r x n e1 e1' e2' :
      web_exp_n n e1' e2' ->
      closed_exp e1 ->
      occurs_free e1' \subset [set x] ->
      web_exp_n n (link_w lft x e1 e1') (link_w lft x e1 e2').
    Proof.
      intros Hrel. revert e1. induction Hrel; intros e1 Hc Hfv.
      - econstructor; [| | eassumption ].
        + eapply E_web_preserves_linking; eauto. eapply E_web_refl; eauto.
        + intros z Hz. exfalso.
          assert (Hfv2 : occurs_free c2 \subset [set x]) by (eapply Included_trans; eauto).
          destruct (link_closed lft x e1 c2 Hc Hfv2) as [Hl _]. eapply Hl in Hz. inv Hz.
      - econstructor; [ eapply IHHrel1; eauto | eapply IHHrel2; eauto ].
        eapply Included_trans; [| eassumption ]. eapply R_n_preserves_fv; eauto.
    Qed.

    (** Lemma 7.6: linking for λweb *)
    Theorem web_exp_n_preserves_linking x n m e1 e2 e1' e2' :
      web_exp_n n e1 e2 ->
      web_exp_n m e1' e2' ->
      closed_exp e1 ->
      occurs_free e1' \subset [set x] ->
      web_exp_n (n + m) (link_w lft x e1 e1') (link_w lft x e2 e2').
    Proof.
      intros Hrel1 Hrel2 Hc1 Hfv.
      eapply R_n_trans. eapply web_exp_n_preserves_linking_src_l; eauto.
      eapply web_exp_n_preserves_linking_src_r; eauto.
      eapply closed_preserves_fv; eauto. eapply R_n_preserves_fv; eauto.
    Qed.

  End LinkingComp.

End Types.
