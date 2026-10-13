(* Reflexivity of the λweb relation.

   We instantiate the parameterized relation with the identity-shaped
   relation for internal closures ([VT_id]: internal closures are related
   like exposed ones, except that their arguments and results need not be
   exposed), prove the fundamental property for it by induction on terms
   (the compatibility lemmas), and conclude with Corollary 5.2 that every
   term is related to itself by the λweb relation. *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics algebra set_util.
From CertiRocq.LambdaANF Require term term_util.
From CertiRocq.LambdaWeb Require Import syntax semantics exposed post compat indep.

Import ListNotations.

Open Scope alg_scope.

Section Refl.

  Variable (cenv : term.ctor_env).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Local Notation PostT := (@exposed.PostT fuel trace).
  Local Notation PostGT := (@exposed.PostGT fuel trace).
  Local Notation VTransT := (@exposed.VTransT fuel trace).

  Definition VT_id : VTransT := fun PG V' k v1 v2 => V_fun cenv PG V' k v1 v2.

  Global Instance VTransProps_id : VTransProps VT_id.
  Proof.
    constructor; unfold VT_id; intros.
    - eapply V_fun_ext; eauto.
    - eapply V_fun_mono; eauto.
  Qed.

  Context (P : PostT) (PG : PostGT) {Hprops : Post_properties cenv P P PG}.

  Lemma P_PG : inclusion _ P PG.
  Proof. destruct Hprops; assumption. Qed.

  Notation V := (V cenv VT_id PG).
  Notation E := (E cenv VT_id PG).
  Notation G := (G cenv VT_id PG).
  Notation var_rel := (var_rel cenv VT_id PG).

  Lemma var_rel_id_fun k rho1 rho2 f1 f2 w :
    var_rel k rho1 rho2 f1 f2 -> fun_rel cenv VT_id PG k rho1 rho2 f1 f2 w.
  Proof.
    intros Hvar v1 Hget. edestruct Hvar as (v2 & Hget2 & Hv); eauto.
    eexists; split; eauto. intros Hweb. destruct v1; simpl in Hweb; try congruence.
    destruct (exposedb w) eqn:Hw.
    - eapply V_exposed_fun; eauto.
    - eapply V_internal_fun in Hv; eauto.
      rewrite exposed_val_Vfun. intros (w' & xs & e & Hfn' & Hw'). unfold fun_web in Hweb.
      rewrite Hfn' in Hweb. inv Hweb. congruence.
  Qed.

  (** Closures of the same bundle defined in related environments are
      related, provided bodies are related at smaller indices. *)
  Lemma Vfun_id k rho1 rho2 B f :
    (forall m ex e rho1 rho2,
        m < k ->
        G m (occurs_free e) rho1 rho2 ->
        E P ex m (e, rho1) (e, rho2)) ->
    G k (occurs_free_fundefs B) rho1 rho2 ->
    name_in_fundefs B f ->
    V k (Vfun rho1 B f) (Vfun rho2 B f).
  Proof.
    revert f. induction k as [k IHk] using lt_wf_rec. intros f Hexp HG Hin.
    edestruct name_in_fundefs_find_def as (w & xs & e & Hfind); eauto.
    assert (Hfun : V_fun cenv PG V k (Vfun rho1 B f) (Vfun rho2 B f)).
    { eapply V_fun_def; eauto.
      intros j vs1 vs2 rho1' rho2' Hlt Hexpv Hvs Hset1 Hset2.
      eapply E_post_mono; [ exact P_PG |].
      eapply Hexp; [ eassumption |].
      eapply G_antimon; [| eapply occurs_free_in_fun; eassumption ].
      eapply G_set_lists; eauto.
      eapply G_def_funs.
      - eapply G_antimon. eapply G_mono; eauto. lia.
        eapply fun_body_scope_subset.
      - eapply HG. - eapply HG.
      - reflexivity.
      - intros g Hg. eapply IHk; eauto.
        + intros. eapply Hexp; eauto. lia.
        + eapply G_mono; eauto. lia. }
    destruct (exposedb w) eqn:Hw.
    - eapply V_Vfun_exposed; eauto; apply HG.
    - eapply V_Vfun_internal; eauto; try apply HG.
      + constructor. apply HG.
      + rewrite exposed_val_Vfun. intros (w' & xs' & e' & Hfn' & Hw'). congruence.
      + rewrite exposed_val_Vfun. intros (w' & xs' & e' & Hfn' & Hw'). congruence.
  Qed.

  (** The fundamental property of the identity instantiation *)
  Lemma fundamental k ex e rho1 rho2 :
    G k (occurs_free e) rho1 rho2 ->
    E P ex k (e, rho1) (e, rho2).
  Proof.
    revert ex e rho1 rho2.
    induction k as [k IH] using lt_wf_rec.
    intros ex e. revert k IH ex.
    induction e using exp_ind'; intros k IH ex rho1 rho2 HG; pose proof Hprops as Hprops'; destruct Hprops'.
    - (* Econstr *)
      eapply E_constr_compat; eauto.
      + eapply G_Forall2_var_rel; eauto. normalize_occurs_free. sets.
      + intros m v1 v2 Hlt Hv. eapply IHe.
        * intros. eapply IH; eauto. lia.
        * eapply G_set; eauto. eapply G_antimon. eapply G_mono; eauto. lia.
          normalize_occurs_free. sets.
    - (* Ecase [] *)
      eapply E_case_nil_compat; eauto.
    - (* Ecase (_ :: _) *)
      eapply E_case_cons_compat; eauto.
      + eapply Forall2_refl. intros []; reflexivity.
      + eapply G_var_rel; eauto. fv_mem.
      + intros m Hlt. eapply IHe.
        * intros. eapply IH; eauto. lia.
        * eapply G_antimon. eapply G_mono; eauto. lia.
          normalize_occurs_free. sets.
      + eapply IHe0; eauto.
        eapply G_antimon; eauto. normalize_occurs_free. sets.
    - (* Eproj *)
      eapply E_proj_compat; eauto.
      + eapply G_var_rel; eauto. fv_mem.
      + intros m v1 v2 Hlt Hv. eapply IHe.
        * intros. eapply IH; eauto. lia.
        * eapply G_set; eauto. eapply G_antimon. eapply G_mono; eauto. lia.
          normalize_occurs_free. sets.
    - (* Eletapp *)
      eapply E_letapp_compat; eauto.
      + eapply var_rel_id_fun. eapply G_var_rel; eauto. fv_mem.
      + eapply G_Forall2_var_rel; eauto. normalize_occurs_free. sets.
      + intros m v1 v2 Hlt _ Hv. eapply IHe.
        * intros. eapply IH; eauto. lia.
        * eapply G_set; eauto. eapply G_antimon. eapply G_mono; eauto. lia.
          normalize_occurs_free. sets.
    - (* Efun *)
      eapply E_fun_compat; eauto.
      eapply IHe.
      + intros. eapply IH; eauto. lia.
      + eapply G_antimon; [| eapply occurs_free_Efun_Included ].
        eapply G_def_funs.
        * eapply G_antimon. eapply G_mono; eauto. lia.
          intros z Hz. inv Hz. inv H; eauto. exfalso; eauto.
        * eapply HG.
        * eapply HG.
        * reflexivity.
        * intros f Hfn. eapply Vfun_id; eauto.
          -- intros. eapply IH; eauto. lia.
          -- eapply G_antimon. eapply G_mono; eauto. lia.
             eapply occurs_free_fundefs_Efun_Included.
    - (* Eapp *)
      eapply E_app_compat; eauto.
      + eapply var_rel_id_fun. eapply G_var_rel; eauto. fv_mem.
      + eapply G_Forall2_var_rel; eauto. normalize_occurs_free. sets.
    - (* Eprim_val *)
      eapply E_stuck_compat; eauto. intros. eapply Eprim_val_stuck.
    - (* Eprim *)
      eapply E_stuck_compat; eauto. intros. eapply Eprim_stuck.
    - (* Ehalt *)
      eapply E_halt_compat; eauto.
      eapply G_var_rel; eauto. fv_mem.
  Qed.

  Lemma E_top_id e : E_top cenv VT_id P PG e e.
  Proof. intros k rho1 rho2 [HG _] Hbind. eapply fundamental; eauto. Qed.

  (** Every term is related to itself by the λweb relation. *)
  Theorem E_web_refl e : E_web cenv P PG e e.
  Proof. exact (E_top_E_web cenv VT_id P PG e e (E_top_id e)). Qed.

End Refl.
