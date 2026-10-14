(* The compiler of [LambdaWeb/passes.v] with the 0-CFA as its analysis.

     λANF ⇝ λANF ⇝ 0-CFA ⇝ DPE ⇝ CP ⇝ defunc ⇝ erase ⇝ λANF ⇝ λANF

   The analysis and erasure keep the steps of the program, so both use the
   postcondition that equates the fuel of the two programs.  The only
   remaining hypotheses are the correctness of the λANF optimizations. *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics algebra set_util.
From CertiRocq.LambdaANF Require term identifiers bounds.
From CertiRocq.LambdaANF Require eval rel_comp.
From CertiRocq.LambdaWeb Require Import syntax semantics comp anno erase pipeline passes.
From CertiRocq.LambdaCFA Require Import spec sound impl.

Import ListNotations.

Module ANF := CertiRocq.LambdaANF.rel_comp.

Existing Instance bounds.fuel_res.
Existing Instance bounds.trace_res.

Notation fuel := nat.
Notation trace := (nat * nat)%type.

Open Scope alg_scope.

(** * Erasure keeps the steps of the program *)

Definition P_eq_e : @PostT_e fuel trace :=
  fun p1 p2 => let '(_, _, c1, _) := p1 in let '(_, _, c2, _) := p2 in c1 = c2.

Lemma P_eq_e_properties cenv tagf : Post_properties_e cenv tagf P_eq_e P_eq_e P_eq_e.
Proof.
  constructor; try (intros c1 c2 H; exact H);
    unfold P_eq_e; repeat intro; simpl in *; subst; reflexivity.
Qed.

Lemma P_eq_e_upper_bound : post_e_upper_bound P_eq_e.
Proof.
  intros e1 rho1 e2 rho2. exists (fun c => c).
  intros cin1 cin2 cout1 cout2 H. simpl in H. subst.
  exists <0>. rewrite plus_zero. reflexivity.
Qed.

(** * The compiler *)

Section Compiler.

  Variables (anf_opt1 anf_opt2 : term.ctor_env -> term.exp -> term.exp).

  (** The interface: the web of exposed constructors *)
  Variable (w_con : web).
  Hypothesis (Hw_con : exposedb w_con = true).

  Hypotheses (Hopt1 : forall cenv e, exists n, anf_n cenv n e (anf_opt1 cenv e))
             (Hopt2 : forall cenv e, exists n, anf_n cenv n e (anf_opt2 cenv e)).

  Definition compile_cfa (cenv : term.ctor_env) (e : term.exp) : term.ctor_env * term.exp :=
    compile anf_opt1 anf_opt2 (fun _ => annotate w_con) (fun w _ => web_tag w) cenv e.

  Theorem compile_cfa_refines cenv e :
    identifiers.closed_exp e ->
    let '(cenv', e5) := compile_cfa cenv e in
    cenv_ext cenv cenv' /\
    (forall v1 c1 t1,
        CertiRocq.LambdaANF.eval.bstep_fuel cenv ANF.emp e c1 (CertiRocq.LambdaANF.eval.Res v1) t1 ->
        exists v2 c2 t2,
          CertiRocq.LambdaANF.eval.bstep_fuel cenv' ANF.emp e5 c2 (CertiRocq.LambdaANF.eval.Res v2) t2 /\
          ANF.value_ref v1 v2) /\
    (CertiRocq.LambdaANF.eval.diverge cenv ANF.emp e -> CertiRocq.LambdaANF.eval.diverge cenv' ANF.emp e5).
  Proof.
    eapply (compile_refines anf_opt1 anf_opt2 (fun _ => annotate w_con) w_con (fun w _ => web_tag w) P_eq P_eq P_eq_e P_eq_e
                            P_eq_upper_bound P_eq_e_upper_bound (fun cenv => P_eq_e_properties cenv _) Hopt1 Hopt2).
    intros cenv' e'. eapply annotate_correct. exact Hw_con.
  Qed.

  (** Separately compiled units, each annotated by its own run of the
      analysis, can be linked: the annotation relation is compatible with
      linking (Lemma 7.4) at the postconditions of the analysis. *)
  Theorem annotate_preserves_linking cenv lft x e1 e2 :
    identifiers.closed_exp e1 ->
    identifiers.occurs_free e2 \subset [set x] ->
    E_anno_top cenv w_con P_eq P_eq (CertiRocq.LambdaANF.rel_comp.link lft x e1 e2)
               (link_w lft x (annotate w_con e1) (annotate w_con e2)).
  Proof.
    intros Hc Hfv. eapply E_anno_preserves_linking; eauto.
    - eapply P_eq_properties.
    - eapply annotate_correct; eauto.
    - eapply annotate_correct; eauto.
  Qed.

  (** Linking does not require both units to use this analysis: the
      library or the client may be annotated by any analysis proven against
      [E_anno_top] at the same interface ([w_con], [Exposed t] for exposed
      functions) and postconditions, e.g. a context-sensitive one. *)
  Theorem annotate_links_with_lib cenv lft x e1 e1' e2' :
    identifiers.closed_exp e1 ->
    identifiers.occurs_free e1' \subset [set x] ->
    E_anno_top cenv w_con P_eq P_eq e1' e2' ->
    E_anno_top cenv w_con P_eq P_eq (CertiRocq.LambdaANF.rel_comp.link lft x e1 e1')
               (link_w lft x (annotate w_con e1) e2').
  Proof.
    intros Hc Hfv H'. eapply E_anno_preserves_linking; eauto.
    - eapply P_eq_properties.
    - eapply annotate_correct; eauto.
  Qed.

  Theorem annotate_links_with_client cenv lft x e1 e2 e1' :
    identifiers.closed_exp e1 ->
    identifiers.occurs_free e1' \subset [set x] ->
    E_anno_top cenv w_con P_eq P_eq e1 e2 ->
    E_anno_top cenv w_con P_eq P_eq (CertiRocq.LambdaANF.rel_comp.link lft x e1 e1')
               (link_w lft x e2 (annotate w_con e1')).
  Proof.
    intros Hc Hfv H. eapply E_anno_preserves_linking; eauto.
    - eapply P_eq_properties.
    - eapply annotate_correct; eauto.
  Qed.

End Compiler.
