(* Top-level correctness of the λANF pipeline with the web optimizations
   ([toplevel.v], [-O 2]).

   The web step

     hoist ⇝ 0-CFA ⇝ defunc ⇝ arity raising ⇝ DPE ⇝ CP ⇝ erase ⇝ freshen

   is a λANF step, an annotation, λweb steps, an erasure and a λANF step:
   the relation [pipeline_rel] of [LambdaWeb/pipeline.v].  A first web step
   runs before lambda lifting, without hoisting and defunctionalization;
   the passes up to closure conversion are a chain of λANF and web steps
   ([pre_rel]), which refines and links one step at a time.  Defunctionalization
   adds constructors to the constructor environment, so the relations of
   the step hold in any environment that extends the extended one, and the
   compiled program is evaluated in it.  The λANF passes are correct in any
   environment.

   The theorem for whole programs: the compiled program refines the source,
   the source evaluated in the environment the pipeline starts with, and the
   compiled program in an extension of it.

   Linking: units compiled separately, each with or without the web
   optimizations, link.  Internal webs get tags from a fixed function
   ([retag.tagf_glob]), so all units erase with the same tag function, and
   a unit compiled without the web step is related through λweb by the
   trivial annotation, which erases back to it.  The linked program is
   evaluated in an environment that extends the environments of both
   units. *)

From Stdlib Require Import NArith.BinNat Relations.Relations Lists.List micromega.Lia Sets.Ensembles.

Require Import LambdaANF.term LambdaANF.eval LambdaANF.term_util LambdaANF.identifiers LambdaANF.set_util
        LambdaANF.Ensembles_util LambdaANF.List_util LambdaANF.tactics LambdaANF.rel_comp
        LambdaANF.bounds LambdaANF.shrink_cps_toplevel LambdaANF.toplevel LambdaANF.toplevel_theorems
        LambdaANF.freshen LambdaANF.freshen_correct.
Require Import Common.compM.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaWeb Require syntax semantics comp anno erase pipeline passes retag hoist hoist_correct
     dfn_impl ar_impl dpe_impl cp_impl.
From CertiRocq.LambdaCFA Require fast compile sound.

Require Import ExtLib.Structures.Monad.
Import ListNotations MonadNotation.
Open Scope monad_scope.

Close Scope Z_scope.
Local Open Scope nat_scope.

Existing Instance bounds.fuel_res.
Existing Instance bounds.trace_res.

(** * λANF evaluation in an extended constructor environment *)

Lemma bstep_fuel_cenv_ext cenv cenv' rho e c r t :
  passes.cenv_ext cenv cenv' ->
  bstep_fuel cenv rho e c r t -> bstep_fuel cenv' rho e c r t.
Proof.
  intros Hext H.
  eapply (@bstep_fuel_ind' cenv _ _ _ _
            (fun rho e c r t => bstep cenv' rho e c r t)
            (fun rho e c r t => bstep_fuel cenv' rho e c r t)); eauto;
    intros; try (econstructor; eauto; fail).
  econstructor; eauto. eapply dfn_impl.caseConsistent_ext; eauto.
Qed.

Lemma diverge_cenv_ext cenv cenv' rho e :
  passes.cenv_ext cenv cenv' -> diverge cenv rho e -> diverge cenv' rho e.
Proof.
  intros Hext Hd c. destruct (Hd c) as [t Ht]. exists t. eapply bstep_fuel_cenv_ext; eassumption.
Qed.

Lemma cenv_ext_trans c1 c2 c3 : passes.cenv_ext c1 c2 -> passes.cenv_ext c2 c3 -> passes.cenv_ext c1 c3.
Proof. intros H1 H2 c i H. eauto. Qed.

(** The compiled program refines the source, evaluated in two environments *)
Definition refines_ext (cenv cenv' : ctor_env) (vref : val -> val -> Prop) (e1 e2 : exp) :=
  (forall v1 c1 t1, bstep_fuel cenv rel_comp.emp e1 c1 (Res v1) t1 ->
                    exists v2 c2 t2, bstep_fuel cenv' rel_comp.emp e2 c2 (Res v2) t2 /\ vref v1 v2) /\
  (diverge cenv rel_comp.emp e1 -> diverge cenv' rel_comp.emp e2).

(** * The relations *)

Definition w_con := syntax.Exposed 1%positive.

Lemma Hw_con : syntax.exposedb w_con = true.
Proof. reflexivity. Qed.

(** The web step *)
Definition web_rel (cenv : ctor_env) (e1 e2 : exp) : Prop :=
  exists n1 n2 n3,
    pipeline.pipeline_rel cenv w_con sound.P_eq sound.P_eq retag.tagf_glob compile.P_eq_e compile.P_eq_e n1 n2 n3 e1 e2.

(** The passes up to closure conversion: λANF steps and web steps *)
Inductive pre_rel (cenv : ctor_env) : exp -> exp -> Prop :=
| Pre_anf : forall n e1 e2, pipeline.anf_n cenv n e1 e2 -> pre_rel cenv e1 e2
| Pre_web : forall e1 e2, web_rel cenv e1 e2 -> pre_rel cenv e1 e2
| Pre_trans : forall e1 e2 e3, pre_rel cenv e1 e2 -> pre_rel cenv e2 e3 -> pre_rel cenv e1 e3.

Lemma anf_n_refl cenv e : pipeline.anf_n cenv 1 e e.
Proof. eapply preord_exp_n_refl. intros e1 z Hz; exact Hz. Qed.

(** The whole pipeline *)
Definition top_rel (cenv : ctor_env) (e1 e2 : exp) : Prop :=
  exists e, pre_rel cenv e1 e /\
            exists n m, R_n_exp cenv clo_tag wf_pres (post_prop cenv) (simple_bound 0) (simple_bound 0) n m e e2.

(** The specification of the pipeline: from the environment [cenv0], the
    compilation extends it to [cenvw], and the relation holds in any
    extension of [cenvw]. *)
Definition correct_w (cenv0 : ctor_env) (trans : anf_trans) :=
  forall e c,
    well_scoped e ->
    (max_var e 1 < state.next_var c)%positive ->
    exists e' c',
      trans e c = (Ret e', c') /\
      well_scoped e' /\
      (max_var e' 1 < state.next_var c')%positive /\
      exists cenvw, dfn_impl.dfn_ext cenv0 cenvw /\
                    forall cenv, passes.cenv_ext cenvw cenv -> top_rel cenv e e'.

(** The specification of a web step without defunctionalization: the
    constructor environment is unchanged *)
Definition correct_web0 (cenv0 : ctor_env) (trans : anf_trans) :=
  forall e c,
    well_scoped e ->
    (max_var e 1 < state.next_var c)%positive ->
    exists e' c',
      trans e c = (Ret e', c') /\
      well_scoped e' /\
      (max_var e' 1 < state.next_var c')%positive /\
      forall cenv, passes.cenv_ext cenv0 cenv -> pre_rel cenv e e'.

(** The specification of the web step *)
Definition correct_web (cenv0 : ctor_env) (trans : anf_trans) :=
  forall e c,
    well_scoped e ->
    (max_var e 1 < state.next_var c)%positive ->
    exists e' c',
      trans e c = (Ret e', c') /\
      well_scoped e' /\
      (max_var e' 1 < state.next_var c')%positive /\
      exists cenvw, dfn_impl.dfn_ext cenv0 cenvw /\
                    forall cenv, passes.cenv_ext cenvw cenv -> pre_rel cenv e e'.

(** * Composition *)

Transparent bind.

Lemma pre_rel_anf_l cenv n e1 e2 e3 :
  pipeline.anf_n cenv n e1 e2 -> pre_rel cenv e2 e3 -> pre_rel cenv e1 e3.
Proof. intros H1 H2. eapply Pre_trans; [ eapply Pre_anf; eassumption | exact H2 ]. Qed.

Lemma correct_w_compose_l cenv0 (t1 t2 : anf_trans) :
  (forall cenv, correct cenv t1) ->
  correct_w cenv0 t2 ->
  correct_w cenv0 (fun e => e <- t1 e;; t2 e).
Proof.
  intros Ht1 Ht2 e c Hws Hmax.
  destruct (Ht1 cenv0 e c Hws Hmax) as (e1 & c1 & Hr1 & Hws1 & Hmax1 & _).
  destruct (Ht2 e1 c1 Hws1 Hmax1) as (e2 & c2 & Hr2 & Hws2 & Hmax2 & cenvw & Hext & Hrel).
  exists e2, c2. split; [ simpl; unfold bind; cbn; rewrite Hr1, Hr2; reflexivity |].
  split; [ exact Hws2 | split; [ exact Hmax2 |] ].
  exists cenvw. split; [ exact Hext |]. intros cenv Hc.
  destruct (Ht1 cenv e c Hws Hmax) as (e1' & c1' & Hr1' & _ & _ & n & Hn).
  rewrite Hr1 in Hr1'. inv Hr1'.
  destruct (Hrel cenv Hc) as (e3 & Hpre & Hcc).
  exists e3. split; [| exact Hcc ]. eapply pre_rel_anf_l; eassumption.
Qed.

Lemma correct_w_time cenv0 (t : anf_trans) o s :
  correct_w cenv0 t -> correct_w cenv0 (time_anf o s t).
Proof. unfold time_anf. intros H. destruct (time o); eauto. Qed.

Lemma correct_web_time cenv0 (t : anf_trans) o s :
  correct_web cenv0 t -> correct_web cenv0 (time_anf o s t).
Proof. unfold time_anf. intros H. destruct (time o); eauto. Qed.

Lemma correct_web0_time cenv0 (t : anf_trans) o s :
  correct_web0 cenv0 t -> correct_web0 cenv0 (time_anf o s t).
Proof. unfold time_anf. intros H. destruct (time o); eauto. Qed.

Lemma correct_w_web0 cenv0 (t1 t2 : anf_trans) :
  correct_web0 cenv0 t1 ->
  correct_w cenv0 t2 ->
  correct_w cenv0 (fun e => e <- t1 e;; t2 e).
Proof.
  intros Ht1 Ht2 e c Hws Hmax.
  destruct (Ht1 e c Hws Hmax) as (e1 & c1 & Hr1 & Hws1 & Hmax1 & Hrel1).
  destruct (Ht2 e1 c1 Hws1 Hmax1) as (e2 & c2 & Hr2 & Hws2 & Hmax2 & cenvw & Hext & Hrel).
  exists e2, c2. split; [ simpl; unfold bind; cbn; rewrite Hr1, Hr2; reflexivity |].
  split; [ exact Hws2 | split; [ exact Hmax2 |] ].
  exists cenvw. split; [ exact Hext |]. intros cenv Hc.
  destruct (Hrel cenv Hc) as (e3 & Hpre & Hcc).
  exists e3. split; [| exact Hcc ]. eapply Pre_trans; [| exact Hpre ].
  eapply Hrel1. eapply cenv_ext_trans; [ exact (proj1 Hext) | exact Hc ].
Qed.

Lemma correct_w_web cenv0 (t1 t2 : anf_trans) :
  correct_web cenv0 t1 ->
  (forall cenv, correct_cc cenv clo_tag t2) ->
  correct_w cenv0 (fun e => e <- t1 e;; t2 e).
Proof.
  intros Ht1 Ht2 e c Hws Hmax.
  destruct (Ht1 e c Hws Hmax) as (e1 & c1 & Hr1 & Hws1 & Hmax1 & cenvw & Hext & Hrel).
  destruct (Ht2 cenv0 e1 c1 Hws1 Hmax1) as (e2 & c2 & Hr2 & Hws2 & Hmax2 & _).
  exists e2, c2. split; [ simpl; unfold bind; cbn; rewrite Hr1, Hr2; reflexivity |].
  split; [ exact Hws2 | split; [ exact Hmax2 |] ].
  exists cenvw. split; [ exact Hext |]. intros cenv Hc.
  destruct (Ht2 cenv e1 c1 Hws1 Hmax1) as (e2' & c2' & Hr2' & _ & _ & n & m & Hnm).
  rewrite Hr2 in Hr2'. inv Hr2'.
  exists e1. split; [ exact (Hrel cenv Hc) | exists n, m; exact Hnm ].
Qed.

Lemma correct_web_id cenv0 : correct_web cenv0 id_trans.
Proof.
  intros e c Hws Hmax. exists e, c. split; [ reflexivity |]. split; [ exact Hws | split; [ exact Hmax |] ].
  exists cenv0. split; [ eapply dfn_impl.dfn_ext_refl |]. intros cenv _. eapply Pre_anf. eapply anf_n_refl.
Qed.

(** * The web step *)

Theorem web_trans_correct cenv0 : correct_web cenv0 (web_trans cenv0).
Proof.
  intros e c Hws Hmax.
  destruct c as [nv nc ni nf cenvc fenv names imap log].
  pose proof Hws as [Hun Hdis].
  unfold web_trans, web_trans_gen. cbn beta iota.
  set (eh := hoist.hoist e).
  match goal with |- context [ fast.analyze_fast ?w ?ee ] => destruct (fast.analyze_fast w ee) as [sl x] eqn:Han end.
  match goal with |- context [ dfn_impl.dfn_top cenv0 ?ee ] => set (e0 := ee) end.
  assert (He0 : e0 = fast.annotate_fast w_con eh) by (unfold fast.annotate_fast; unfold w_con; rewrite Han; reflexivity).
  pose proof (passes.dfn_top_web_n_ext cenv0 e0) as Hd.
  pose proof (dfn_impl.dfn_top_ext cenv0 e0) as Hext.
  destruct (dfn_impl.dfn_top cenv0 e0) as [cenv' ed] eqn:Hdfn. destruct Hd as [_ Hd]. simpl in Hext.
  set (ew := cp_impl.cp_top (dpe_impl.dpe_top (ar_impl.ar_top (dpe_impl.dpe_top ed)))).
  set (e' := erase.erase_t retag.tagf_glob ew).
  destruct (retag.fenv_of ew (fenv, true, 1%positive)) as [[fenv' tags_ok] maxt] eqn:Hfe.
  destruct (andb tags_ok (fnd e')) eqn:Hok.
  - apply andb_prop in Hok as [_ Hfnd].
    match goal with
    | |- context [ freshen_top e' ?c' ] =>
        assert (Hmax' : (max_var e' 1 < state.next_var c')%positive) by (simpl; lia);
        destruct (freshen_top_correct e' c' Hmax' Hfnd) as (ef & cf & Hfr & Ha & Hubf & Hdisf & Hfvf & Hmaxf)
    end.
    unfold web_note. rewrite Hfr.
    exists ef, cf. split; [ reflexivity |]. split; [ split; assumption |]. split; [ exact Hmaxf |].
    exists cenv'. split; [ exact Hext |]. intros cenv Hc. eapply Pre_web.
    exists 1, 5, 1.
    destruct (hoist_correct.hoist_top_correct cenv e Hun Hdis) as (nh & Hsem & _ & _ & Hfvh & _).
    exists eh. split.
    { econstructor 1 with (P1 := hoisting_bound nh nh) (P2 := hoisting_bound nh nh).
      - intros k rho1 rho2 Henv _. eapply Hsem. exact Henv.
      - exact Hfvh.
      - split; [ eapply hoisting_bound_compat; lia | eapply hoisting_bound_post_upper_bound ]. }
    exists e0. split.
    { rewrite He0. eapply fast.annotate_fast_correct. exact Hw_con. }
    exists ew. split.
    { change 5 with (1 + 1 + 1 + 1 + 1).
      eapply comp.R_n_trans; [ eapply comp.R_n_trans; [ eapply comp.R_n_trans; [ eapply comp.R_n_trans |] |] |].
      - eapply Hd. exact Hc.
      - eapply passes.dpe_web_n.
      - eapply passes.ar_web_n.
      - eapply passes.dpe_web_n.
      - eapply passes.cp_web_n. }
    exists e'. split.
    { eapply erase.erase_correct. eapply compile.P_eq_e_properties. }
    econstructor 1 with (P1 := simple_bound 0) (P2 := simple_bound 0).
    + intros k rho1 rho2 Henv _. eapply Alpha_conv_id_preord; [ eapply simple_bound_compat | exact Ha | exact Henv ].
    + intros z Hz. apply Hfvf. exact Hz.
    + split; [ eapply simple_bound_compat | eapply simple_bound_post_upper_bound ].
  - exists e. eexists. split; [ reflexivity |]. split; [ exact Hws | split; [ exact Hmax |] ].
    exists cenv0. split; [ eapply dfn_impl.dfn_ext_refl |]. intros cenv _. eapply Pre_anf. eapply anf_n_refl.
Qed.

(** The web step before lambda lifting, without defunctionalization *)
Theorem web_trans_pre_correct cenv0 : correct_web0 cenv0 (web_trans_pre cenv0).
Proof.
  intros e c Hws Hmax.
  destruct c as [nv nc ni nf cenvc fenv names imap log].
  pose proof Hws as [Hun Hdis].
  unfold web_trans_pre, web_trans_gen. cbn beta iota.
  match goal with |- context [ fast.analyze_fast ?w ?ee ] => destruct (fast.analyze_fast w ee) as [sl x] eqn:Han end.
  set (e0 := impl.anno (syntax.Exposed 1) sl e).
  assert (He0 : e0 = fast.annotate_fast w_con e) by (unfold fast.annotate_fast; unfold w_con; rewrite Han; reflexivity).
  set (ew := cp_impl.cp_top (dpe_impl.dpe_top (ar_impl.ar_top (dpe_impl.dpe_top e0)))).
  set (e' := erase.erase_t retag.tagf_glob ew).
  destruct (retag.fenv_of ew (fenv, true, 1%positive)) as [[fenv' tags_ok] maxt] eqn:Hfe.
  destruct (andb tags_ok (fnd e')) eqn:Hok.
  - apply andb_prop in Hok as [_ Hfnd].
    match goal with
    | |- context [ freshen_top e' ?c' ] =>
        assert (Hmax' : (max_var e' 1 < state.next_var c')%positive) by (simpl; lia);
        destruct (freshen_top_correct e' c' Hmax' Hfnd) as (ef & cf & Hfr & Ha & Hubf & Hdisf & Hfvf & Hmaxf)
    end.
    unfold web_note. rewrite Hfr.
    exists ef, cf. split; [ reflexivity |]. split; [ split; assumption |]. split; [ exact Hmaxf |].
    intros cenv Hc. eapply Pre_web.
    exists 1, 4, 1.
    exists e. split; [ eapply anf_n_refl |].
    exists e0. split.
    { rewrite He0. eapply fast.annotate_fast_correct. exact Hw_con. }
    exists ew. split.
    { change 4 with (1 + 1 + 1 + 1).
      eapply comp.R_n_trans; [ eapply comp.R_n_trans; [ eapply comp.R_n_trans |] |].
      - eapply passes.dpe_web_n.
      - eapply passes.ar_web_n.
      - eapply passes.dpe_web_n.
      - eapply passes.cp_web_n. }
    exists e'. split.
    { eapply erase.erase_correct. eapply compile.P_eq_e_properties. }
    econstructor 1 with (P1 := simple_bound 0) (P2 := simple_bound 0).
    + intros k rho1 rho2 Henv _. eapply Alpha_conv_id_preord; [ eapply simple_bound_compat | exact Ha | exact Henv ].
    + intros z Hz. apply Hfvf. exact Hz.
    + split; [ eapply simple_bound_compat | eapply simple_bound_post_upper_bound ].
  - exists e. eexists. split; [ reflexivity |]. split; [ exact Hws | split; [ exact Hmax |] ].
    intros cenv _. eapply Pre_anf. eapply anf_n_refl.
Qed.

(** * The pipeline *)

Theorem anf_chain_web_correct v opts cenv0 :
  webs opts = true -> correct_w cenv0 (anf_chain v opts cenv0).
Proof.
  intros Hw. unfold anf_chain.
  eapply correct_w_compose_l. { intros cenv. eapply correct_time. now eapply shrink_err_correct. }
  eapply correct_w_compose_l. { intros cenv. eapply correct_time. now eapply uncurry_top_correct_corr. }
  eapply correct_w_compose_l. { intros cenv. eapply correct_time. now eapply inline_uncurry_cor. }
  eapply correct_w_compose_l.
  { intros cenv. destruct (inl_before opts).
    eapply correct_time. now eapply inline_loop_correct. now eapply correct_id_trans. }
  rewrite Hw. eapply correct_w_web0. { eapply correct_web0_time. eapply web_trans_pre_correct. }
  eapply correct_w_compose_l.
  { intros cenv. destruct (do_lambda_lift opts).
    eapply correct_time. now eapply lambda_lift_correct_corr. now eapply correct_id_trans. }
  eapply correct_w_compose_l. { intros cenv. now eapply correct_id_trans. }
  eapply correct_w_web. { eapply correct_web_time. eapply web_trans_correct. }
  intros cenv.
  eapply correct_cc_compose_r.
  eapply correct_cc_time. now eapply closure_conversion_hoist_correct.
  eapply correct_compose.
  eapply correct_time. now eapply shrink_err_correct.
  eapply correct_compose.
  destruct (inl_after opts).
  eapply correct_time. now eapply inline_loop_correct.
  now eapply correct_id_trans.
  eapply correct_compose.
  destruct (dpe opts).
  eapply correct_time. now eapply DPE_correct_corr.
  now eapply correct_id_trans.
  eapply correct_compose.
  eapply correct_time. now eapply shrink_err_correct.
  eapply correct_compose.
  destruct (inl_known opts).
  eapply correct_time.
  unfold inline_lifted. now eapply inline_correct_cor.
  now eapply correct_id_trans.
  now eapply correct_id_trans.
Qed.

(** * Whole programs *)

Lemma pre_rel_preserves_fv cenv e1 e2 :
  pre_rel cenv e1 e2 -> occurs_free e2 \subset occurs_free e1.
Proof.
  intros H. induction H as [n e1 e2 H | e1 e2 (n1 & n2 & n3 & e3 & H13 & e4 & H34 & e5 & H45 & e6 & H56 & H62) |].
  - eapply pipeline.anf_n_preserves_fv. eassumption.
  - eapply Included_trans; [| eapply pipeline.anf_n_preserves_fv; eassumption ].
    eapply Included_trans; [| eapply H34 ].
    eapply Included_trans; [| eapply pipeline.web_n_preserves_fv; eassumption ].
    eapply Included_trans; [ eapply pipeline.anf_n_preserves_fv; eassumption | eapply H56 ].
  - eapply Included_trans; eassumption.
Qed.

Lemma pre_rel_step_refines cenv e1 e2 :
  closed_exp e1 -> ((exists n, pipeline.anf_n cenv n e1 e2) \/ web_rel cenv e1 e2) -> refines cenv value_ref e1 e2.
Proof.
  intros Hc [[n H] | (n1 & n2 & n3 & H)].
  - eapply pipeline.anf_n_refines; eassumption.
  - eapply pipeline.pipeline_refines; eauto;
      first [ exact Hw_con | eapply sound.P_eq_properties | eapply sound.P_eq_upper_bound
            | eapply compile.P_eq_e_properties | eapply compile.P_eq_e_upper_bound ].
Qed.

Lemma closed_pre_rel cenv e1 e2 : closed_exp e1 -> pre_rel cenv e1 e2 -> closed_exp e2.
Proof.
  intros Hc H. split; [| sets ]. eapply Included_trans; [ eapply pre_rel_preserves_fv; eassumption | eapply Hc ].
Qed.

(** A chain of steps, followed by closure conversion and the rest *)
Lemma pre_rel_refines_cc cenv e1 e2 e3 :
  closed_exp e1 -> pre_rel cenv e1 e2 -> refines cenv value_ref_cc e2 e3 -> refines cenv value_ref_cc e1 e3.
Proof.
  intros Hc H. revert e3 Hc. induction H as [n e1 e2 H | e1 e2 H | e1 e2 e4 H1 IH1 H2 IH2]; intros e3 Hc Hr.
  2: assert (Hs : refines cenv value_ref e1 e2) by (eapply pre_rel_step_refines; eauto).
  1: assert (Hs : refines cenv value_ref e1 e2) by (eapply pre_rel_step_refines; eauto).
  1, 2: destruct Hs as [Ht1 Hd1]; destruct Hr as [Ht2 Hd2]; split;
    [ intros v1 c1 t1 Hs; edestruct Ht1 as (v2 & c2 & t2 & Hs2 & Hr2); [ exact Hs |];
      edestruct Ht2 as (v3 & c3 & t3 & Hs3 & Hr3); [ exact Hs2 |];
      do 3 eexists; split; [ exact Hs3 | eapply value_ref_compose_l; eassumption ]
    | intros Hdiv; eapply Hd2, Hd1; exact Hdiv ].
  eapply IH1; [ exact Hc |]. eapply IH2; [ eapply closed_pre_rel; eassumption | exact Hr ].
Qed.

Lemma top_rel_refines_ext cenvA cenvB e1 e2 :
  closed_exp e1 -> passes.cenv_ext cenvA cenvB -> top_rel cenvB e1 e2 ->
  refines_ext cenvA cenvB value_ref_cc e1 e2.
Proof.
  intros Hc Hext (e & Hpre & n & m & Hcc).
  assert (Hce : closed_exp e).
  { split; [| sets ]. eapply Included_trans; [ eapply pre_rel_preserves_fv; eassumption | eapply Hc ]. }
  assert (Href : refines cenvB value_ref_cc e e2).
  { eapply R_n_exp_in_refines; eauto.
    clear; now firstorder.
    clear; now firstorder.
    eapply simple_bound_post_upper_bound. }
  destruct (pre_rel_refines_cc _ _ _ _ Hc Hpre Href) as [Ht Hd].
  split.
  - intros v1 c1 t1 Hs. eapply bstep_fuel_cenv_ext in Hs; [| exact Hext ]. eauto.
  - intros Hdiv. eapply Hd. eapply diverge_cenv_ext; eassumption.
Qed.

(** The compiled program refines the source, the source evaluated in the
    environment the pipeline starts with, and the compiled program in an
    extension of it (by the constructors of defunctionalization). *)
Theorem anf_pipeline_whole_program_correct' v opts e c :
  closed_exp e ->
  well_scoped e ->
  (max_var e 1 < state.next_var c)%positive ->
  exists e' c',
    anf_pipeline v opts e c = (Ret e', c') /\
    exists cenv', dfn_impl.dfn_ext (state.cenv c) cenv' /\
                  refines_ext (state.cenv c) cenv' value_ref_cc e e'.
Proof.
  intros Hc Hws Hmax. unfold anf_pipeline.
  destruct (webs opts) eqn:Hw.
  - destruct (anf_chain_web_correct v opts (state.cenv c) Hw e c Hws Hmax)
      as (e' & c' & Hr & _ & _ & cenvw & Hext & Hrel).
    exists e', c'. split; [ exact Hr |]. exists cenvw. split; [ exact Hext |].
    eapply top_rel_refines_ext; [ exact Hc | exact (proj1 Hext) | eapply Hrel; eapply passes.cenv_ext_refl ].
  - destruct (anf_chain_correct (state.cenv c) opts v (state.cenv c) Hw e c Hws Hmax)
      as (e' & c' & Hr & _ & _ & n & m & Hcc).
    exists e', c'. split; [ exact Hr |]. exists (state.cenv c). split; [ eapply dfn_impl.dfn_ext_refl |].
    eapply top_rel_refines_ext; [ exact Hc | eapply passes.cenv_ext_refl |].
    exists e. split; [ eapply Pre_anf; eapply anf_n_refl |].
    exists n, m. exact Hcc.
Qed.

(** * Linking *)

(** The trivial annotation: every function is exposed with its λANF tag as
    its web.  It erases back to the program, so a unit compiled without the
    web optimizations is also related through λweb, and links with units
    compiled with them. *)
Lemma erase_anno_triv :
  (forall e, erase.erase_t retag.tagf_glob (impl.anno w_con impl.triv e) = e) /\
  (forall B, erase.erase_t_fundefs retag.tagf_glob (impl.anno_fds w_con impl.triv B) = B).
Proof.
  eapply exp_def_mutual_ind; intros; simpl; try reflexivity; try congruence.
  match goal with
  | IHe : erase.erase_t _ (impl.anno _ _ ?e) = ?e, IHl : erase.erase_t _ (impl.anno _ _ (Ecase _ _)) = _ |- _ =>
      simpl in IHl; injection IHl as IHl'; rewrite IHe; f_equal; f_equal; exact IHl'
  end.
Qed.

Lemma anno_triv_correct cenv e :
  anno.E_anno_top cenv w_con sound.P_eq sound.P_eq e (impl.anno w_con impl.triv e).
Proof. eapply (sound.ok_top_E_anno cenv w_con Hw_con impl.triv). eapply impl.triv_top. Qed.

Lemma pre_rel_web cenv e1 e2 : ((exists n, pipeline.anf_n cenv n e1 e2) \/ web_rel cenv e1 e2) -> web_rel cenv e1 e2.
Proof.
  intros [[n H] | H]; [| exact H ].
  exists n, 1, 1.
  exists e2. split; [ exact H |].
  exists (impl.anno w_con impl.triv e2). split; [ eapply anno_triv_correct |].
  exists (impl.anno w_con impl.triv e2). split; [ eapply passes.web_n_refl |].
  exists e2. split.
  - pose proof (compile.P_eq_e_properties cenv retag.tagf_glob) as Hpp.
    pose proof (erase.erase_correct cenv retag.tagf_glob compile.P_eq_e compile.P_eq_e
                  (impl.anno w_con impl.triv e2)) as He.
    rewrite (proj1 erase_anno_triv) in He. eapply He.
  - eapply preord_exp_n_refl. intros e3 z Hz; exact Hz.
Qed.

(** The pipeline, with or without the web optimizations *)
Theorem anf_pipeline_spec v opts e c :
  well_scoped e ->
  (max_var e 1 < state.next_var c)%positive ->
  exists e' c',
    anf_pipeline v opts e c = (Ret e', c') /\
    exists cenvw, dfn_impl.dfn_ext (state.cenv c) cenvw /\
                  forall cenv, passes.cenv_ext cenvw cenv -> top_rel cenv e e'.
Proof.
  intros Hws Hmax. unfold anf_pipeline.
  destruct (webs opts) eqn:Hw.
  - destruct (anf_chain_web_correct v opts (state.cenv c) Hw e c Hws Hmax)
      as (e' & c' & Hr & _ & _ & cenvw & Hext & Hrel).
    exists e', c'. split; [ exact Hr |]. exists cenvw. split; [ exact Hext | exact Hrel ].
  - destruct (anf_chain_correct (state.cenv c) opts v (state.cenv c) Hw e c Hws Hmax)
      as (e' & c' & Hr & _ & _ & _).
    exists e', c'. split; [ exact Hr |]. exists (state.cenv c). split; [ eapply dfn_impl.dfn_ext_refl |].
    intros cenv _.
    destruct (anf_chain_correct cenv opts v (state.cenv c) Hw e c Hws Hmax)
      as (e'' & c'' & Hr' & _ & _ & n & m & Hcc).
    rewrite Hr in Hr'. inv Hr'.
    exists e. split; [ eapply Pre_anf; eapply anf_n_refl |].
    exists n, m. exact Hcc.
Qed.

Lemma web_rel_preserves_linking cenv lf x e1 e2 e1' e2' :
  closed_exp e1 ->
  occurs_free e2 \subset [set x] ->
  web_rel cenv e1 e1' ->
  web_rel cenv e2 e2' ->
  web_rel cenv (link lf x e1 e2) (link lf x e1' e2').
Proof.
  intros Hc Hfv (a1 & b1 & c1 & Hp1) (a2 & b2 & c2 & Hp2).
  exists (a1 + a2), (b1 + b2), (c1 + c2).
  eapply pipeline.pipeline_preserves_linking; eauto;
    first [ exact Hw_con | eapply sound.P_eq_properties | eapply retag.tagf_glob_exposed
          | eapply compile.P_eq_e_properties ].
Qed.

Lemma web_rel_refl cenv e : web_rel cenv e e.
Proof. eapply pre_rel_web. left. exists 1. eapply anf_n_refl. Qed.

(** Linking, one unit at a time *)
Lemma pre_rel_link_l cenv lf x e1 e1' e2 :
  closed_exp e1 -> occurs_free e2 \subset [set x] ->
  pre_rel cenv e1 e1' -> pre_rel cenv (link lf x e1 e2) (link lf x e1' e2).
Proof.
  intros Hc Hfv H. induction H as [n e1 e1' H | e1 e1' H | e1 e3 e1' H1 IH1 H2 IH2].
  - eapply Pre_web. eapply web_rel_preserves_linking; eauto using web_rel_refl.
    eapply pre_rel_web. left. eexists; eassumption.
  - eapply Pre_web. eapply web_rel_preserves_linking; eauto using web_rel_refl.
  - eapply Pre_trans; [ eapply IH1; exact Hc | eapply IH2; eapply closed_pre_rel; eassumption ].
Qed.

Lemma pre_rel_link_r cenv lf x e1 e2 e2' :
  closed_exp e1 -> occurs_free e2 \subset [set x] ->
  pre_rel cenv e2 e2' -> pre_rel cenv (link lf x e1 e2) (link lf x e1 e2').
Proof.
  intros Hc Hfv H. induction H as [n e2 e2' H | e2 e2' H | e2 e3 e2' H1 IH1 H2 IH2].
  - eapply Pre_web. eapply web_rel_preserves_linking; eauto using web_rel_refl.
    eapply pre_rel_web. left. eexists; eassumption.
  - eapply Pre_web. eapply web_rel_preserves_linking; eauto using web_rel_refl.
  - eapply Pre_trans; [ eapply IH1; exact Hfv | eapply IH2 ].
    eapply Included_trans; [ eapply pre_rel_preserves_fv; eassumption | exact Hfv ].
Qed.

Lemma top_rel_preserves_linking cenv lf x e1 e2 e1' e2' :
  closed_exp e1 ->
  occurs_free e2 \subset [set x] ->
  top_rel cenv e1 e1' ->
  top_rel cenv e2 e2' ->
  top_rel cenv (link lf x e1 e2) (link lf x e1' e2').
Proof.
  intros Hc Hfv (m1 & Hpre1 & n1 & k1 & Hcc1) (m2 & Hpre2 & n2 & k2 & Hcc2).
  assert (Hcm : closed_exp m1) by (eapply closed_pre_rel; eassumption).
  exists (link lf x m1 m2). split.
  - eapply Pre_trans; [ eapply pre_rel_link_l; eassumption | eapply pre_rel_link_r; eassumption ].
  - exists (n1 + n2), (k1 + k2). eapply Rel_exp_n_preserves_linking; eauto.
    + intros. eapply H.
    + eapply simple_bound_compat.
    + eapply Included_trans; [ eapply pre_rel_preserves_fv; eassumption | exact Hfv ].
Qed.

(** Separately compiled units link, each with or without the web
    optimizations.  Each unit extends the constructor environment it starts
    with; the linked program is evaluated in any environment that extends
    both, and the source in any environment it extends.  Such an
    environment always exists ([anf_pipeline_linking_correct] below). *)
Theorem anf_pipeline_linking_correct' lf x v1 v2 o1 o2 e1 e2 c1 c2 :
  closed_exp e1 ->
  well_scoped e1 ->
  (max_var e1 1 < state.next_var c1)%positive ->
  occurs_free e2 \subset [set x] ->
  well_scoped e2 ->
  (max_var e2 1 < state.next_var c2)%positive ->
  exists e1' e2' c1' c2',
    anf_pipeline v1 o1 e1 c1 = (Ret e1', c1') /\
    anf_pipeline v2 o2 e2 c2 = (Ret e2', c2') /\
    exists cenv1 cenv2,
      dfn_impl.dfn_ext (state.cenv c1) cenv1 /\
      dfn_impl.dfn_ext (state.cenv c2) cenv2 /\
      forall cenv cenv',
        passes.cenv_ext cenv1 cenv' -> passes.cenv_ext cenv2 cenv' -> passes.cenv_ext cenv cenv' ->
        refines_ext cenv cenv' value_ref_cc (link lf x e1 e2) (link lf x e1' e2').
Proof.
  intros Hc1 Hws1 Hmax1 Hfv2 Hws2 Hmax2.
  destruct (anf_pipeline_spec v1 o1 e1 c1 Hws1 Hmax1) as (e1' & c1' & Hr1 & cenv1 & Hext1 & Hrel1).
  destruct (anf_pipeline_spec v2 o2 e2 c2 Hws2 Hmax2) as (e2' & c2' & Hr2 & cenv2 & Hext2 & Hrel2).
  exists e1', e2', c1', c2'. split; [ exact Hr1 | split; [ exact Hr2 |] ].
  exists cenv1, cenv2. split; [ exact Hext1 | split; [ exact Hext2 |] ].
  intros cenv cenv' H1 H2 H3.
  eapply top_rel_refines_ext; [ eapply link_closed; eassumption | exact H3 |].
  eapply top_rel_preserves_linking; [ exact Hc1 | exact Hfv2 | eapply Hrel1; exact H1 | eapply Hrel2; exact H2 ].
Qed.

(** * Linking without disjoint constructors

    Defunctionalization gives its constructors tags in a reserved range,
    with information that is a function of the tag ([dfn_impl.dfn_info]).
    Units that pick the same tag therefore agree on its constructor, so the
    environments of any two units have a common extension, provided the
    source environment does not use the reserved range. *)

Definition unreserved (cenv : ctor_env) : Prop :=
  forall c i, cenv ! c = Some i -> (c < dfn_impl.res_base)%positive.

Definition pick {A} (o1 o2 : option A) : option A :=
  match o1 with Some _ => o1 | None => o2 end.

Lemma dfn_ext_join b1 x1 b2 x2 cenv :
  dfn_impl.dfn_ext b1 x1 -> dfn_impl.dfn_ext b2 x2 ->
  passes.cenv_ext b1 cenv -> passes.cenv_ext b2 cenv -> unreserved cenv ->
  exists cenv', passes.cenv_ext x1 cenv' /\ passes.cenv_ext x2 cenv' /\ passes.cenv_ext cenv cenv'.
Proof.
  intros [_ H1] [_ H2] Hb1 Hb2 Hu.
  set (m := PTree.combine pick cenv x1).
  exists (PTree.combine pick m x2).
  assert (Hm : forall c, m ! c = pick (cenv ! c) (x1 ! c)) by (intros c; unfold m; rewrite PTree.gcombine; reflexivity).
  assert (Hg : forall c, (PTree.combine pick m x2) ! c = pick (m ! c) (x2 ! c))
    by (intros c; rewrite PTree.gcombine; reflexivity).
  assert (Hres : forall c i, (dfn_impl.res_base <= c)%positive -> cenv ! c = Some i -> False)
    by (intros c i Hc Hci; specialize (Hu c i Hci); lia).
  split; [| split ].
  - intros c i Hc. rewrite Hg, Hm. destruct (H1 c i Hc) as [Hb | [Hr ->]].
    + rewrite (Hb1 _ _ Hb). reflexivity.
    + destruct (cenv ! c) eqn:Hce; [ exfalso; eapply Hres; eassumption |]. simpl. rewrite Hc. reflexivity.
  - intros c i Hc. rewrite Hg, Hm. destruct (H2 c i Hc) as [Hb | [Hr ->]].
    + rewrite (Hb2 _ _ Hb). reflexivity.
    + destruct (cenv ! c) eqn:Hce; [ exfalso; eapply Hres; eassumption |]. simpl.
      destruct (x1 ! c) eqn:Hx1; [| simpl; rewrite Hc; reflexivity ].
      destruct (H1 c _ Hx1) as [Hb | [_ ->]]; [| reflexivity ].
      rewrite (Hb1 _ _ Hb) in Hce. discriminate.
  - intros c i Hc. rewrite Hg, Hm, Hc. reflexivity.
Qed.

(** Separately compiled units link, each with or without the web
    optimizations: the linked program is evaluated in an extension of the
    source environment, which only has to avoid the reserved tags. *)
Theorem anf_pipeline_linking_correct lf x v1 v2 o1 o2 e1 e2 c1 c2 :
  closed_exp e1 ->
  well_scoped e1 ->
  (max_var e1 1 < state.next_var c1)%positive ->
  occurs_free e2 \subset [set x] ->
  well_scoped e2 ->
  (max_var e2 1 < state.next_var c2)%positive ->
  exists e1' e2' c1' c2',
    anf_pipeline v1 o1 e1 c1 = (Ret e1', c1') /\
    anf_pipeline v2 o2 e2 c2 = (Ret e2', c2') /\
    forall cenv,
      passes.cenv_ext (state.cenv c1) cenv -> passes.cenv_ext (state.cenv c2) cenv -> unreserved cenv ->
      exists cenv', passes.cenv_ext cenv cenv' /\
                    refines_ext cenv cenv' value_ref_cc (link lf x e1 e2) (link lf x e1' e2').
Proof.
  intros Hc1 Hws1 Hmax1 Hfv2 Hws2 Hmax2.
  destruct (anf_pipeline_linking_correct' lf x v1 v2 o1 o2 e1 e2 c1 c2 Hc1 Hws1 Hmax1 Hfv2 Hws2 Hmax2)
    as (e1' & e2' & c1' & c2' & Hr1 & Hr2 & cenv1 & cenv2 & Hx1 & Hx2 & Hall).
  exists e1', e2', c1', c2'. split; [ exact Hr1 | split; [ exact Hr2 |] ].
  intros cenv Hb1 Hb2 Hu.
  destruct (dfn_ext_join _ _ _ _ _ Hx1 Hx2 Hb1 Hb2 Hu) as (cenv' & H1 & H2 & H3).
  exists cenv'. split; [ exact H3 | eapply Hall; eassumption ].
Qed.
