(* The implemented λweb passes in the compositional pipeline.

   Each implementation (DPE, constant propagation, defunctionalization) is a
   step of [web_exp_n], the transitive closure of the λweb relation, so they
   compose with each other and with linking (comp.v).  Defunctionalization
   adds the constructors of its lambda sets to the constructor environment:
   it is a step of [web_exp_n] for the extended environment, and the passes
   before it, which do not depend on the environment, are steps for the
   extended environment as well.

   We then build a compiler

     λANF ⇝ λANF ⇝ λweb ⇝ DPE ⇝ CP ⇝ defunc ⇝ λANF ⇝ λANF

   from λANF optimizations and an annotation function (the flow analysis),
   and prove that it refines the behavior of closed programs, the source
   running with the original constructor environment and the output with
   the extended one. *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations Classes.RelationClasses.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics algebra set_util.
From CertiRocq.LambdaANF Require term term_util identifiers bounds.
From CertiRocq.LambdaANF Require eval rel_comp.
From CertiRocq.LambdaWeb Require Import syntax semantics exposed post compat bound indep refl comp
     dpe dpe_impl cp cp_impl ar ar_impl defunc dfn_impl erase anno pipeline.

Import ListNotations.

Module ANF := CertiRocq.LambdaANF.rel_comp.

Existing Instance bounds.fuel_res.
Existing Instance bounds.trace_res.

Notation fuel := nat.
Notation trace := (nat * nat)%type.

(** * Each pass is a step of [web_exp_n] *)

Section Steps.

  Variable (cenv : term.ctor_env).

  Lemma dead_bound_web_post G : web_post_prop cenv (dead_bound G G) (dead_bound G G).
  Proof. split; [ eapply dead_bound_properties; lia | eapply dead_bound_upper_bound ]. Qed.

  Lemma P_ge_web_post : web_post_prop cenv (P_ge : @exposed.PostT fuel trace) P_ge.
  Proof. split; [ eapply P_ge_properties | eapply P_ge_upper_bound ]. Qed.

  Theorem dpe_web_n e : web_n cenv 1 e (dpe_top e).
  Proof.
    econstructor; [ eapply dpe_top_correct | | eapply dead_bound_web_post ].
    eapply (proj1 (dpe.trans_occurs_free (masks e) (esize e))). eapply dpe_top_trans.
  Qed.

  Theorem cp_web_n e : web_n cenv 1 e (cp_top e).
  Proof.
    econstructor; [ eapply cp_top_correct | | eapply dead_bound_web_post ].
    eapply (proj1 (cp.trans_occurs_free (choose_map e) (esize e))). eapply cp_top_trans.
  Qed.

  Theorem ar_web_n e : web_n cenv 1 e (ar_top e).
  Proof.
    econstructor; [ eapply ar_top_correct | | eapply dead_bound_web_post ].
    eapply (proj1 (ar.trans_occurs_free (ar_choose e))). eapply ar_top_trans.
  Qed.

  (** The specification of defunctionalization, given its hypotheses *)
  Theorem dfn_trans_web_n L T Btop e et :
    (forall w lams, WM.get w L = Some lams ->
                    exists it, Forall (fun c => exists info, M.get c cenv = Some info /\
                                                             term.ctor_ind_tag info = it) lams) ->
    (forall c code wc n args, T ! c = Some (code, wc, n, args) -> Code Btop code) ->
    trans_top L T Btop e et -> web_n cenv 1 e et.
  Proof.
    intros HL HT Htop. econstructor; [ | | eapply P_ge_web_post ].
    - eapply dfn_correct_top; eassumption.
    - eapply trans_top_preserves_fv; eassumption.
  Qed.

  Lemma web_n_refl e : web_n cenv 1 e e.
  Proof.
    econstructor; [ eapply (E_web_refl cenv P_ge P_ge) | | eapply P_ge_web_post ].
    intros z Hz; exact Hz.
  Qed.

End Steps.

(** ** Defunctionalization extends the constructor environment *)

Definition cenv_ext (cenv cenv' : term.ctor_env) : Prop :=
  forall c i, cenv ! c = Some i -> cenv' ! c = Some i.

Lemma cenv_ext_refl cenv : cenv_ext cenv cenv.
Proof. intros c i H; exact H. Qed.

Theorem dfn_top_web_n cenv e :
  let '(cenv', et) := dfn_top cenv e in
  cenv_ext cenv cenv' /\ web_n cenv' 1 e et.
Proof.
  unfold dfn_top.
  destruct e; try (split; [ eapply cenv_ext_refl | eapply web_n_refl ]).
  match goal with
  | [ |- context [ if ?b then _ else _ ] ] =>
      destruct b eqn:Hchk; [| split; [ eapply cenv_ext_refl | eapply web_n_refl ] ]
  end.
  repeat match goal with
         | [ H : (_ && _) = true |- _ ] => apply andb_true_iff in H; destruct H
         end.
  set (r := analyze_dfn cenv f e) in *.
  set (m := identifiers.max_var (erase (Efun f e)) 1%positive) in *.
  set (jw := Pos.succ (max_iweb (Efun f e))) in *.
  split.
  { intros c i Hci. unfold r. rewrite r_cenv_eq. eapply ext_check_spec; eauto. }
  eapply (dfn_trans_web_n (r_cenv r) (r_L r) (r_T r) f);
    [ eapply hl_check_spec; eassumption | eapply ht_check_spec; eassumption |].
  do 3 eexists. split; [ reflexivity | split; [ reflexivity |] ].
  split; [| split ].
  - match goal with
    | [ Hk : forallb (sel_w _) (fd_webs f) = true, Hfd : dfn_ok_fd _ _ _ _ _ _ [] [] f = true |- _ ] =>
        pose proof (proj2 (dfn_ok_trans _ _ _ _ _ _ jw) f [] [] Hfd) as Hb;
        rewrite (recs_with_keep _ _ _ _ Hk) in Hb; exact Hb
    end.
  - rewrite <- bnames_fnames. eapply nodupb_spec. eassumption.
  - eapply (proj1 (dfn_ok_trans _ _ _ _ _ _ jw)). eassumption.
Qed.

(** * The λweb optimizer *)

Definition web_opt (cenv : term.ctor_env) (e : exp) : term.ctor_env * exp :=
  dfn_top cenv (cp_top (dpe_top e)).

Theorem web_opt_web_n cenv e :
  let '(cenv', et) := web_opt cenv e in
  cenv_ext cenv cenv' /\ web_n cenv' 3 e et.
Proof.
  unfold web_opt. pose proof (dfn_top_web_n cenv (cp_top (dpe_top e))) as Hd.
  destruct (dfn_top cenv (cp_top (dpe_top e))) as [cenv' et]. destruct Hd as [Hext Hd].
  split; [ exact Hext |].
  change 3 with (1 + 1 + 1). eapply R_n_trans; [ eapply R_n_trans |].
  - eapply dpe_web_n.
  - eapply cp_web_n.
  - exact Hd.
Qed.

(** Evaluation is preserved by extending the constructor environment. *)
Lemma refines_cenv_ext cenv cenv' e :
  cenv_ext cenv cenv' ->
  (forall v1 c1 t1, bstep_fuel cenv true emp e c1 (Res v1) t1 ->
                    exists v2 c2 t2, bstep_fuel cenv' true emp e c2 (Res v2) t2 /\ value_ref v1 v2) /\
  (diverge cenv true emp e -> diverge cenv' true emp e).
Proof.
  intros Hext. split.
  - intros v1 c1 t1 Hs. do 3 eexists. split; [ eapply bstep_cenv_ext; eassumption | eapply value_ref_refl ].
  - intros Hd c. destruct (Hd c) as [t Ht]. eexists. eapply bstep_cenv_ext; eassumption.
Qed.

(** * A compiler through λweb *)

Section Compiler.

  (** λANF optimizations and the annotation (flow analysis), each correct
      for the constructor environment it is given *)
  Variables (anf_opt1 anf_opt2 : term.ctor_env -> term.exp -> term.exp)
            (annotate : term.ctor_env -> term.exp -> exp).

  (** The interface: the web of exposed constructors *)
  Variable (w_con : web).
  Hypothesis (Hw_con : exposedb w_con = true).

  Variables (Pa PGa : @PostT_a fuel trace) (Pe PGe : @PostT_e fuel trace).
  Hypotheses (HPa_ub : post_a_upper_bound Pa) (HPe_ub : post_e_upper_bound Pe).
  Hypotheses (HPe : forall cenv, Post_properties_e cenv Pe Pe PGe).

  Hypotheses (Hopt1 : forall cenv e, exists n, anf_n cenv n e (anf_opt1 cenv e))
             (Hopt2 : forall cenv e, exists n, anf_n cenv n e (anf_opt2 cenv e))
             (Hanno : forall cenv e, anno_rel cenv w_con Pa PGa e (annotate cenv e)).

  (** The compiler returns the extended constructor environment along with
      the program. *)
  Definition compile (cenv : term.ctor_env) (e : term.exp) : term.ctor_env * term.exp :=
    let '(cenv', e3) := web_opt cenv (annotate cenv (anf_opt1 cenv e)) in
    (cenv', anf_opt2 cenv' (erase e3)).

  Theorem compile_refines cenv e :
    identifiers.closed_exp e ->
    let '(cenv', e5) := compile cenv e in
    cenv_ext cenv cenv' /\
    (forall v1 c1 t1,
        CertiRocq.LambdaANF.eval.bstep_fuel cenv ANF.emp e c1 (CertiRocq.LambdaANF.eval.Res v1) t1 ->
        exists v2 c2 t2,
          CertiRocq.LambdaANF.eval.bstep_fuel cenv' ANF.emp e5 c2 (CertiRocq.LambdaANF.eval.Res v2) t2 /\
          ANF.value_ref v1 v2) /\
    (CertiRocq.LambdaANF.eval.diverge cenv ANF.emp e -> CertiRocq.LambdaANF.eval.diverge cenv' ANF.emp e5).
  Proof.
    intros Hc. unfold compile.
    set (e1 := anf_opt1 cenv e). set (e2 := annotate cenv e1).
    pose proof (web_opt_web_n cenv e2) as Hw.
    destruct (web_opt cenv e2) as [cenv' e3]. destruct Hw as [Hext H23].
    destruct (Hopt1 cenv e) as [n1 H01]. fold e1 in H01.
    pose proof (Hanno cenv e1) as H12. fold e2 in H12.
    pose proof (HPe cenv') as HPe'. pose proof (erase_correct cenv' Pe PGe e3) as H34.
    destruct (Hopt2 cenv' (erase e3)) as [n3 H45].
    split; [ exact Hext |].
    assert (Hc1 : identifiers.closed_exp e1)
      by (eapply anf_closed; eauto; eapply anf_n_preserves_fv; eauto).
    assert (Hc2 : closed_exp e2).
    { split; [| sets ]. eapply Included_trans; [ eapply H12 | eapply Hc1 ]. }
    assert (Hc3 : closed_exp e3).
    { eapply closed_preserves_fv; eauto. eapply web_n_preserves_fv; eauto. }
    assert (Hc4 : identifiers.closed_exp (erase e3)).
    { split; [| sets ]. eapply Included_trans; [ eapply H34 | eapply Hc3 ]. }
    pose proof (anf_n_refines _ _ _ _ Hc H01) as [Ht01 Hd01].
    pose proof (E_anno_refines cenv w_con Pa PGa HPa_ub e1 e2 Hc1 H12) as [Ht12 Hd12].
    pose proof (refines_cenv_ext cenv cenv' e2 Hext) as [Htx Hdx].
    pose proof (web_exp_n_refines cenv' preserves_fv (web_post_prop cenv') (fun _ _ H => H)
                                  (fun P PG H => proj2 H) 3 e2 e3 Hc2 H23) as [Ht23 Hd23].
    pose proof (E_erase_refines cenv' Pe PGe HPe_ub e3 (erase e3) Hc3 H34) as [Ht34 Hd34].
    pose proof (anf_n_refines _ _ _ _ Hc4 H45) as [Ht45 Hd45].
    split.
    - intros v0 c0 t0 Hs.
      edestruct Ht01 as (v1 & c1 & t1 & Hs1 & Hr1); eauto.
      edestruct Ht12 as (v2 & c2 & t2 & Hs2 & Hr2); eauto.
      edestruct Htx as (v2' & c2' & t2' & Hs2' & Hr2'); eauto.
      edestruct Ht23 as (v3 & c3 & t3 & Hs3 & Hr3); eauto.
      edestruct Ht34 as (v4 & c4 & t4 & Hs4 & Hr4); eauto.
      edestruct Ht45 as (v5 & c5 & t5 & Hs5 & Hr5); eauto.
      do 3 eexists. split; eauto.
      eapply ANF.value_ref_transitive; [ eassumption |].
      eapply ANF.value_ref_transitive; [| eassumption ].
      eapply value_ref_a_web_e; [ exact Hr2 | | exact Hr4 ].
      eapply value_ref_trans; [ exact Hr2' | exact Hr3 ].
    - intros Hdiv. eauto 10.
  Qed.

End Compiler.
