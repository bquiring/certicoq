(* Compositional correctness of a pipeline going through λweb (Section 7.5
   of the paper):

     λANF ⇝+ λANF ⇝ λweb ⇝+ λweb ⇝ λANF ⇝+ λANF
     (E_anf+)  (E_anno) (E_web+) (E_erase) (E_anf+)

   The first and last phases are CertiRocq's λANF transformations, related
   by CertiRocq's own [preord_exp_n].  The analysis phase is abstract: any
   annotation function whose output is in the annotation relation can be
   used.  The middle phase is any sequence of λweb transformations (e.g.
   flow-directed DPE), and erasure brings the program back to λANF.

   We prove that the composed relation implies CertiRocq's behavioral
   refinement (termination with related values, and divergence
   preservation; Lemma 7.10), and that it is compatible with linking
   (Lemma 7.11). *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations Classes.RelationClasses.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics algebra set_util.
From CertiRocq.LambdaANF Require term term_util identifiers logical_relations.
From CertiRocq.LambdaANF Require eval rel_comp.
From CertiRocq.LambdaWeb Require Import syntax semantics exposed post compat indep comp erase anno.

Import ListNotations.

Open Scope alg_scope.

Module ANF := CertiRocq.LambdaANF.rel_comp.

Section Pipeline.

  Variable (cenv : term.ctor_env).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Local Notation PostT := (@exposed.PostT fuel trace).
  Local Notation PostGT := (@exposed.PostGT fuel trace).
  Local Notation VTransT := (@exposed.VTransT fuel trace).

  (** The interface of exposed webs: the web of exposed constructors, and
      the function tag used for linking thunks. *)
  Variables (w_con : web) (lft : term.fun_tag).
  Hypothesis (Hw_con : exposedb w_con = true).

  (** ** The relations of each phase *)

  (** CertiRocq's top-level relation for λANF transformations *)
  Definition anf_post_prop : ANF.post_property :=
    fun P PG => logical_relations.Post_properties cenv P P PG /\ logical_relations.post_upper_bound P.

  Definition anf_n n := ANF.preord_exp_n cenv ANF.preserves_fv anf_post_prop n.

  (** The λweb relation *)
  Definition web_post_prop : post_property :=
    fun P PG => Post_properties cenv P P PG /\ post_upper_bound P.

  Definition web_n n := web_exp_n cenv preserves_fv web_post_prop n.

  (** The cross-language relations, at fixed postconditions *)
  Context (Pa PGa : PostT_a) (HPa : Post_properties_a cenv Pa PGa) (HPa_ub : post_a_upper_bound Pa).
  Context (Pe PGe : PostT_e) (HPe : Post_properties_e cenv Pe Pe PGe) (HPe_ub : post_e_upper_bound Pe).

  Definition anno_rel := E_anno_top cenv w_con Pa PGa.
  Definition erase_rel := E_erase_top cenv Pe PGe.

  (** The relation of the whole pipeline *)
  Definition pipeline_rel (n1 n2 n3 : nat) : term.exp -> term.exp -> Prop :=
    compose_rel (anf_n n1)
      (compose_rel anno_rel
         (compose_rel (web_n n2)
            (compose_rel erase_rel (anf_n n3)))).

  (** ** Refinement *)

  Lemma web_n_preserves_fv n e1 e2 : web_n n e1 e2 -> preserves_fv e1 e2.
  Proof. intros H; induction H; eauto. eapply preserves_fv_trans; eauto. Qed.

  Lemma anf_n_preserves_fv n e1 e2 : anf_n n e1 e2 -> ANF.preserves_fv e1 e2.
  Proof. intros H; induction H; eauto. eapply Included_trans; eauto. Qed.

  Lemma anf_closed e1 e2 :
    identifiers.closed_exp e1 -> ANF.preserves_fv e1 e2 -> identifiers.closed_exp e2.
  Proof. intros Hc Hp. split; [| sets ]. eapply Included_trans; [ eapply Hp | eapply Hc ]. Qed.

  Lemma anf_pfv_trans : Transitive ANF.preserves_fv.
  Proof. intros e1 e2 e3 H1 H2. unfold ANF.preserves_fv in *. eapply Included_trans; eauto. Qed.

  Lemma anf_n_refines n e1 e2 :
    identifiers.closed_exp e1 -> anf_n n e1 e2 -> ANF.refines cenv ANF.value_ref e1 e2.
  Proof.
    intros Hc Hrel. split.
    - intros v1 c1 t1 Hs.
      edestruct (ANF.preord_exp_n_impl cenv ANF.preserves_fv anf_post_prop (fun _ _ H => H)
                                        anf_pfv_trans n e1 e2 Hc Hrel ANF.emp ANF.emp _ _ _ Hs)
        as (r2 & c2 & t2 & Hs2 & Hres).
      destruct r2 as [| v2].
      + exfalso. eapply ANF.preord_res_n_OOT_r. eassumption.
      + do 3 eexists. split; eauto. eapply ANF.preord_res_n_in_value_ref. eassumption.
    - intros Hdiv.
      eapply (ANF.preord_exp_n_preserves_divergence cenv ANF.preserves_fv anf_post_prop anf_pfv_trans
                (fun e1 e2 Hp Hc => anf_closed e1 e2 Hc Hp)); eauto.
      intros P PG [_ Hub]. exact Hub.
  Qed.

  Lemma value_ref_a_web_e v1 v2 v3 v4 :
    value_ref_a' v1 v2 -> comp.value_ref v2 v3 -> value_ref_e' v3 v4 -> ANF.value_ref v1 v4.
  Proof.
    revert v2 v3 v4. induction v1 using aval_ind_Forall; intros v2 v3 v4 H1 H2 H3;
      destruct v2; simpl in H1; try contradiction;
      destruct v3; simpl in H2; try contradiction;
      destruct v4; simpl in H3; try contradiction; simpl; destructAll; try congruence; eauto.
    split; eauto.
    repeat match goal with
           | [ Ha : context [ value_ref_a' ] |- _ ] => rewrite Forall2_aux_eq in Ha
           | [ Ha : context [ value_ref_e' ] |- _ ] => rewrite Forall2_aux_eq in Ha
           end.
    match goal with
    | [ Ha : Forall2 value_ref_a' vs ?la, Hw : Forall2 value_ref' ?la ?lb,
        He : Forall2 value_ref_e' ?lb ?lc |- _ ] =>
        clear -H Ha Hw He; revert la lb lc Ha Hw He
    end.
    induction H as [| v vs Hv Hvs IHvs]; intros l2 l3 l4 Ha Hw He; inv Ha; inv Hw; inv He; constructor.
    - rewrite ANF.value_ref_eq. eapply Hv; [ eassumption | eapply value_ref_eq; eassumption | eassumption ].
    - eapply IHvs; eauto.
  Qed.

  (** Lemma 7.10: the pipeline refines the behavior of closed programs. *)
  Theorem pipeline_refines n1 n2 n3 e0 e5 :
    identifiers.closed_exp e0 ->
    pipeline_rel n1 n2 n3 e0 e5 ->
    ANF.refines cenv ANF.value_ref e0 e5.
  Proof.
    intros Hc (e1 & H01 & e2 & H12 & e3 & H23 & e4 & H34 & H45).
    assert (Hc1 : identifiers.closed_exp e1) by (eapply anf_closed; eauto; eapply anf_n_preserves_fv; eauto).
    assert (Hc2 : closed_exp e2).
    { split; [| sets ]. eapply Included_trans; [ eapply H12 | eapply Hc1 ]. }
    assert (Hc3 : closed_exp e3).
    { eapply closed_preserves_fv; eauto. eapply web_n_preserves_fv; eauto. }
    assert (Hc4 : identifiers.closed_exp e4).
    { split; [| sets ]. eapply Included_trans; [ eapply H34 | eapply Hc3 ]. }
    pose proof (anf_n_refines _ _ _ Hc H01) as [Ht01 Hd01].
    pose proof (E_anno_refines cenv w_con Pa PGa HPa_ub e1 e2 Hc1 H12) as [Ht12 Hd12].
    pose proof (web_exp_n_refines cenv preserves_fv web_post_prop (fun _ _ H => H)
                                  (fun P PG H => proj2 H) n2 e2 e3 Hc2 H23) as [Ht23 Hd23].
    pose proof (E_erase_refines cenv Pe PGe HPe_ub e3 e4 Hc3 H34) as [Ht34 Hd34].
    pose proof (anf_n_refines _ _ _ Hc4 H45) as [Ht45 Hd45].
    split.
    - intros v0 c0 t0 Hs.
      edestruct Ht01 as (v1 & c1 & t1 & Hs1 & Hr1); eauto.
      edestruct Ht12 as (v2 & c2 & t2 & Hs2 & Hr2); eauto.
      edestruct Ht23 as (v3 & c3 & t3 & Hs3 & Hr3); eauto.
      edestruct Ht34 as (v4 & c4 & t4 & Hs4 & Hr4); eauto.
      edestruct Ht45 as (v5 & c5 & t5 & Hs5 & Hr5); eauto.
      do 3 eexists. split; eauto.
      eapply ANF.value_ref_transitive; [ eassumption |].
      eapply ANF.value_ref_transitive; [| eassumption ].
      eapply value_ref_a_web_e; eauto.
    - intros Hdiv. eauto 10.
  Qed.

  (** ** Linking *)

  Lemma anf_n_post_props P PG : anf_post_prop P PG -> logical_relations.Post_properties cenv P P PG.
  Proof. intros [H _]; exact H. Qed.

  Lemma web_n_post_props P PG : web_post_prop P PG -> Post_properties cenv P P PG.
  Proof. intros [H _]; exact H. Qed.

  (** Lemma 7.11: linking compatibility of the pipeline.  [e0] is the
      source library and [e0'] the source client, which imports the library
      through [x]. *)
  Theorem pipeline_preserves_linking x n1 n2 n3 m1 m2 m3 e0 e5 e0' e5' :
    identifiers.closed_exp e0 ->
    identifiers.occurs_free e0' \subset [set x] ->
    pipeline_rel n1 n2 n3 e0 e5 ->
    pipeline_rel m1 m2 m3 e0' e5' ->
    pipeline_rel (n1 + m1) (n2 + m2) (n3 + m3)
                 (ANF.link lft x e0 e0') (ANF.link lft x e5 e5').
  Proof.
    intros Hc Hfv (e1 & H01 & e2 & H12 & e3 & H23 & e4 & H34 & H45)
           (e1' & H01' & e2' & H12' & e3' & H23' & e4' & H34' & H45').
    assert (Hc1 : identifiers.closed_exp e1) by (eapply anf_closed; eauto; eapply anf_n_preserves_fv; eauto).
    assert (Hfv1 : identifiers.occurs_free e1' \subset [set x])
      by (eapply Included_trans; [ eapply anf_n_preserves_fv; eauto | eauto ]).
    assert (Hc2 : closed_exp e2).
    { split; [| sets ]. eapply Included_trans; [ eapply H12 | eapply Hc1 ]. }
    assert (Hfv2 : occurs_free e2' \subset [set x]) by (eapply Included_trans; [ eapply H12' | eauto ]).
    assert (Hc3 : closed_exp e3).
    { eapply closed_preserves_fv; eauto. eapply web_n_preserves_fv; eauto. }
    assert (Hfv3 : occurs_free e3' \subset [set x]).
    { eapply Included_trans; [| eapply Hfv2 ]. eapply web_n_preserves_fv; eauto. }
    assert (Hc4 : identifiers.closed_exp e4).
    { split; [| sets ]. eapply Included_trans; [ eapply H34 | eapply Hc3 ]. }
    assert (Hfv4 : identifiers.occurs_free e4' \subset [set x])
      by (eapply Included_trans; [ eapply H34' | eauto ]).
    exists (ANF.link lft x e1 e1'). split.
    { eapply ANF.preord_exp_n_preserves_linking; eauto. eapply anf_n_post_props. }
    exists (link_w lft x e2 e2'). split.
    { eapply E_anno_preserves_linking; eauto. }
    exists (link_w lft x e3 e3'). split.
    { eapply web_exp_n_preserves_linking; eauto. eapply web_n_post_props. }
    exists (ANF.link lft x e4 e4'). split.
    { eapply E_erase_preserves_linking; eauto. }
    eapply ANF.preord_exp_n_preserves_linking; eauto. eapply anf_n_post_props.
  Qed.

  (** ** A compiler through λweb

      Given λANF optimizations correct w.r.t. CertiRocq's relation, an
      annotation function correct w.r.t. the annotation relation (this is
      where a flow analysis will go), and λweb optimizations correct
      w.r.t. the λweb relation, the compiler that runs them in sequence and
      erases the webs is correct.  Erasure itself is proven correct
      ([erase_correct]). *)

  Section Compiler.

    Variables (anf_opt1 anf_opt2 : term.exp -> term.exp)
              (annotate : term.exp -> exp)
              (web_opt : exp -> exp).

    Hypotheses (Hopt1 : forall e, exists n, anf_n n e (anf_opt1 e))
               (Hopt2 : forall e, exists n, anf_n n e (anf_opt2 e))
               (Hanno : forall e, anno_rel e (annotate e))
               (Hweb : forall e, exists n, web_n n e (web_opt e)).

    Definition compile (e : term.exp) : term.exp :=
      anf_opt2 (erase (web_opt (annotate (anf_opt1 e)))).

    Lemma compile_pipeline_rel e : exists n1 n2 n3, pipeline_rel n1 n2 n3 e (compile e).
    Proof.
      destruct (Hopt1 e) as [n1 H1].
      destruct (Hweb (annotate (anf_opt1 e))) as [n2 H2].
      destruct (Hopt2 (erase (web_opt (annotate (anf_opt1 e))))) as [n3 H3].
      exists n1, n2, n3.
      exists (anf_opt1 e). split; [ exact H1 |].
      exists (annotate (anf_opt1 e)). split; [ apply Hanno |].
      exists (web_opt (annotate (anf_opt1 e))). split; [ exact H2 |].
      exists (erase (web_opt (annotate (anf_opt1 e)))). split; [ eapply erase_correct; eauto | exact H3 ].
    Qed.

    Theorem compile_refines e :
      identifiers.closed_exp e -> ANF.refines cenv ANF.value_ref e (compile e).
    Proof.
      intros Hc. destruct (compile_pipeline_rel e) as (n1 & n2 & n3 & Hrel).
      eapply pipeline_refines; eauto.
    Qed.

  End Compiler.

End Pipeline.
