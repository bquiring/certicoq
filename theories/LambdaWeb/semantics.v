(* Big-step semantics of λweb.

   This is CertiRocq's fuel- and trace-indexed big-step semantics for λANF
   (LambdaANF/eval.v), extended with the semantic constraints of webs:

   - the web of a value must match the web of the form that eliminates it
     (projection, case analysis, call);
   - exposed constructors may only package exposed values;
   - exposed functions may only be called on exposed values and must return
     exposed values.

   The last constraint is tracked by the flag [ex] of [bstep]: it is [true]
   when the computation is the body of an exposed function (or a top-level
   program), and then every result it produces must be exposed.

   Fuel and trace resources are the ones of λANF; the cost of a λweb
   expression is the cost of its erasure. *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool micromega.Lia.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics algebra.
From CertiRocq.LambdaANF Require term term_util.
From CertiRocq.LambdaWeb Require Import syntax.

Import ListNotations.

Open Scope alg_scope.

Section EVAL.

  Variable (cenv : term.ctor_env).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  (** Resource units of a λweb expression *)
  Definition one_w {A} {H : @exp_resource A} (e : exp) : A := algebra.one (erase e).

  Inductive bstep (ex : bool) : env -> exp -> fuel -> res -> trace -> Prop :=
  | BStept_constr :
      forall x w t ys e rho vs r cin cout,
        get_list ys rho = Some vs ->
        (exposedb w = true -> Forall exposed_val vs) ->
        bstep_fuel ex (M.set x (Vconstr w t vs) rho) e cin r cout ->
        bstep ex rho (Econstr x w t ys e) cin r cout
  | BStept_proj :
      forall x w t n y e rho vs v r cin cout,
        M.get y rho = Some (Vconstr w t vs) ->
        nthN vs n = Some v ->
        bstep_fuel ex (M.set x v rho) e cin r cout ->
        bstep ex rho (Eproj x w t n y e) cin r cout
  | BStept_case :
      forall y w cl t vs e n rho r cin cout,
        M.get y rho = Some (Vconstr w t vs) ->
        term_util.caseConsistent cenv (erase_branches cl) t ->
        find_tag_nth cl t e n ->
        bstep_fuel ex rho e cin r cout ->
        bstep ex rho (Ecase y w cl) cin r cout
  | BStept_app :
      forall f w ys rho rhoc B f' xs e vs rhoc' r cin cout,
        M.get f rho = Some (Vfun rhoc B f') ->
        get_list ys rho = Some vs ->
        find_def f' B = Some (w, xs, e) ->
        set_lists xs vs (def_funs B B rhoc rhoc) = Some rhoc' ->
        (exposedb w = true -> Forall exposed_val vs) ->
        bstep_fuel (exposedb w) rhoc' e cin r cout ->
        bstep ex rho (Eapp f w ys) cin r cout
  | BStept_letapp :
      forall x f w ys e rho rhoc B f' xs eb vs rhoc' v r cin1 cin2 cout1 cout2,
        M.get f rho = Some (Vfun rhoc B f') ->
        get_list ys rho = Some vs ->
        find_def f' B = Some (w, xs, eb) ->
        set_lists xs vs (def_funs B B rhoc rhoc) = Some rhoc' ->
        (exposedb w = true -> Forall exposed_val vs) ->
        bstep_fuel (exposedb w) rhoc' eb cin1 (Res v) cout1 ->
        bstep_fuel ex (M.set x v rho) e cin2 r cout2 ->
        bstep ex rho (Eletapp x f w ys e) (cin1 <+> cin2) r (cout1 <+> cout2)
  | BStept_letapp_oot :
      forall x f w ys e rho rhoc B f' xs eb vs rhoc' cin cout,
        M.get f rho = Some (Vfun rhoc B f') ->
        get_list ys rho = Some vs ->
        find_def f' B = Some (w, xs, eb) ->
        set_lists xs vs (def_funs B B rhoc rhoc) = Some rhoc' ->
        (exposedb w = true -> Forall exposed_val vs) ->
        bstep_fuel (exposedb w) rhoc' eb cin OOT cout ->
        bstep ex rho (Eletapp x f w ys e) cin OOT cout
  | BStept_fun :
      forall B e rho r cin cout,
        bstep_fuel ex (def_funs B B rho rho) e cin r cout ->
        bstep ex rho (Efun B e) cin r cout
  | BStept_halt :
      forall x v rho,
        M.get x rho = Some v ->
        bstep ex rho (Ehalt x) <0> (Res v) <0>
  with bstep_fuel (ex : bool) : env -> exp -> fuel -> res -> trace -> Prop :=
  | BStepf_OOT :
      forall rho e c,
        c << one_w e ->
        bstep_fuel ex rho e c OOT <0>
  | BStepf_run :
      forall rho e r cin cout,
        bstep ex rho e cin r cout ->
        (ex = true -> exposed_res r) ->
        bstep_fuel ex rho e (cin <+> one_w e) r (cout <+> one_w e).

  Scheme bstep_ind' := Minimality for bstep Sort Prop
    with bstep_fuel_ind' := Minimality for bstep_fuel Sort Prop.

  Definition diverge (ex : bool) (rho : env) (e : exp) : Prop :=
    forall cin, exists cout, bstep_fuel ex rho e cin OOT cout.

  (** * Exposure of results *)

  Lemma bstep_fuel_exposed rho e c r cout :
    bstep_fuel true rho e c r cout -> exposed_res r.
  Proof. intros H; inv H; simpl; eauto. Qed.

  Lemma bstep_fuel_exposed_val rho e c v cout :
    bstep_fuel true rho e c (Res v) cout -> exposed_val v.
  Proof. intros H; eapply bstep_fuel_exposed in H; eauto. Qed.

  Lemma bstep_fuel_exposedb w rho e c v cout :
    bstep_fuel (exposedb w) rho e c (Res v) cout -> exposedb w = true -> exposed_val v.
  Proof. intros H Hw; rewrite Hw in H; eapply bstep_fuel_exposed_val; eauto. Qed.

  (** * Well-formedness of results (Lemma 4.1) *)

  Lemma nthN_Forall {A} (P : A -> Prop) vs n v :
    Forall P vs -> nthN vs n = Some v -> P v.
  Proof.
    revert n; induction vs; intros n Hall Hnth; simpl in *; try congruence.
    inv Hall. destruct n; [ inv Hnth; eauto |].
    destruct p; eauto.
  Qed.

  Lemma bstep_wf_res ex rho e c r cout :
    wf_env rho -> bstep ex rho e c r cout -> wf_res r.
  Proof.
    intros Hwf Hstep. revert Hwf.
    induction Hstep using bstep_ind' with
      (P := fun ex rho e c r cout => wf_env rho -> wf_res r)
      (P0 := fun ex rho e c r cout => wf_env rho -> wf_res r); intros Hwf; simpl; eauto.
    - eapply IHHstep. eapply wf_env_set; eauto. constructor; eauto. eapply wf_env_get_list; eauto.
    - eapply IHHstep. eapply wf_env_set; eauto.
      pose proof (wf_env_get _ _ _ Hwf H) as Hv. inv Hv. eapply nthN_Forall; eauto.
    - pose proof (wf_env_get _ _ _ Hwf H) as Hv. inv Hv.
      eapply IHHstep. eapply wf_env_set_lists; [| eapply (wf_env_get_list rho); eauto | eauto ].
      eapply wf_env_def_funs; eauto.
    - pose proof (wf_env_get _ _ _ Hwf H) as Hv. inv Hv.
      eapply IHHstep0. eapply wf_env_set; eauto.
      eapply (IHHstep : wf_env rhoc' -> wf_res (Res v)).
      eapply wf_env_set_lists; [| eapply (wf_env_get_list rho); eauto | eauto ].
      eapply wf_env_def_funs; eauto.
    - eapply IHHstep. eapply wf_env_def_funs; eauto.
    - eapply wf_env_get; eauto.
  Qed.

  Lemma bstep_fuel_wf_res ex rho e c r cout :
    wf_env rho -> bstep_fuel ex rho e c r cout -> wf_res r.
  Proof. intros Hwf Hs; inv Hs; simpl; eauto. eapply bstep_wf_res; eauto. Qed.

  Lemma bstep_fuel_wf_val ex rho e c v cout :
    wf_env rho -> bstep_fuel ex rho e c (Res v) cout -> wf_val v.
  Proof. intros Hwf Hs. eapply bstep_fuel_wf_res in Hs; eauto. Qed.

  (** * Determinism *)

  Lemma step_deterministic_aux ex rho e r v cin cin' r' v' cout cout' :
    bstep ex rho e cin r cout ->
    bstep ex rho e cin' r' cout' ->
    r = Res v -> r' = Res v' ->
    v = v' /\ cin = cin' /\ cout = cout'.
  Proof.
    set (P := fun ex rho e cin r cout =>
                forall v cin' r' v' cout',
                  bstep ex rho e cin' r' cout' ->
                  r = Res v -> r' = Res v' ->
                  v = v' /\ cin = cin' /\ cout = cout').
    set (P0 := fun ex rho e cin r cout =>
                 forall v cin' r' v' cout',
                   bstep_fuel ex rho e cin' r' cout' ->
                   r = Res v -> r' = Res v' ->
                   v = v' /\ cin = cin' /\ cout = cout').
    intros Hstep.
    revert v cin' r' v' cout'.
    induction Hstep using bstep_ind' with (P := P) (P0 := P0); unfold P, P0 in *;
      intros v1 r2 v2 cin2' cout2' Hstep2 Heq1 Heq2; subst;
      try now (inv Hstep2; repeat subst_exp; eapply IHHstep; eauto).
    - inv Hstep2. repeat subst_exp.
      match goal with
      | [ Ha : find_tag_nth _ _ _ _, Hb : find_tag_nth _ _ _ _ |- _ ] =>
          destruct (find_tag_nth_deterministic _ _ _ _ _ _ Ha Hb); subst
      end.
      eapply IHHstep; eauto.
    - inv Hstep2. repeat subst_exp.
      edestruct IHHstep as (? & ? & ?); [ eassumption | reflexivity | reflexivity | ]. subst.
      edestruct IHHstep0 as (? & ? & ?); [ eassumption | reflexivity | reflexivity | ]. subst.
      eauto.
    - inv Hstep2. inv Heq1. repeat subst_exp. eauto.
    - inv Heq1.
    - inv Hstep2.
      edestruct IHHstep as (? & ? & ?); [ eassumption | reflexivity | reflexivity | ]. subst.
      eauto.
  Qed.

  Lemma bstep_fuel_deterministic ex rho e v cin cin' v' cout cout' :
    bstep_fuel ex rho e cin (Res v) cout ->
    bstep_fuel ex rho e cin' (Res v') cout' ->
    v = v' /\ cin = cin' /\ cout = cout'.
  Proof.
    intros H1 H2; inv H1; inv H2.
    match goal with
    | [ Ha : bstep _ _ _ _ (Res _) _, Hb : bstep _ _ _ _ (Res _) _ |- _ ] =>
        destruct (step_deterministic_aux _ _ _ _ _ _ _ _ _ _ _ Ha Hb eq_refl eq_refl) as (? & ? & ?)
    end.
    subst. eauto.
  Qed.

  (** * Fuel lemmas *)

  Lemma bstep_lt_OOT_aux ex rho e r cin (v : val) cout cin' :
    bstep ex rho e cin r cout ->
    r = Res v ->
    cin' << cin ->
    exists cout' c, bstep ex rho e cin' OOT cout' /\ cout = (c <+> cout').
  Proof.
    set (P := fun ex rho e cin r cout =>
                forall (v : val) cin',
                  r = Res v -> cin' << cin ->
                  exists cout' c, bstep ex rho e cin' OOT cout' /\ cout = (c <+> cout')).
    set (P0 := fun ex rho e cin r cout =>
                 forall (v : val) cin',
                   r = Res v -> cin' << cin ->
                   exists cout' c, bstep_fuel ex rho e cin' OOT cout' /\ cout = (c <+> cout')).
    intros Hstep. revert v cin'.
    induction Hstep using bstep_ind' with (P := P) (P0 := P0); unfold P, P0 in *;
      intros v1 cin' Heq Hlt; subst;
      try (now edestruct IHHstep;
           [reflexivity | eassumption | destructAll; do 2 eexists; split; eauto; econstructor; eauto ]).
    - destruct (lt_all_dec cin' cin1) as [Hlt1 | [z Hz]].
      + edestruct IHHstep as (cout' & c & Hs & Heq); [ reflexivity | eassumption | ]. subst.
        exists cout', (c <+> cout2). split. eapply BStept_letapp_oot; eauto.
        rewrite !plus_assoc, (plus_comm cout' cout2). reflexivity.
      + subst cin'. rewrite (plus_comm cin1) in Hlt. eapply plus_stable in Hlt.
        edestruct IHHstep0 as (cout' & c & Hs & Heq); [ reflexivity | eassumption | ]. subst.
        do 2 eexists. split. rewrite plus_comm.
        eapply BStept_letapp; eauto.
        rewrite <- !plus_assoc. rewrite (plus_comm cout1). reflexivity.
    - inv Heq.
    - eapply lt_zero in Hlt. contradiction.
    - inv Heq.
    - edestruct (lt_all_dec cin' (one_w e)).
      + subst. do 2 eexists. split. econstructor 1; eauto.
        rewrite (plus_comm _ <0>). rewrite plus_zero. reflexivity.
      + destructAll. eapply plus_stable in Hlt.
        edestruct IHHstep. reflexivity. eassumption. destructAll.
        do 2 eexists. split. econstructor 2. eassumption. intros; exact I.
        rewrite plus_assoc. reflexivity.
  Qed.

  Lemma bstep_fuel_lt_OOT ex rho e v cin cout cin' :
    bstep_fuel ex rho e cin (Res v) cout ->
    cin' << cin ->
    exists cout' c, bstep_fuel ex rho e cin' OOT cout' /\ cout = (c <+> cout').
  Proof.
    intros H1 Hlt; inv H1.
    edestruct (lt_all_dec cin' (one_w e)).
    + subst. do 2 eexists. split. econstructor 1; eauto.
      rewrite (plus_comm _ <0>). rewrite plus_zero. reflexivity.
    + destructAll. eapply plus_stable in Hlt.
      edestruct bstep_lt_OOT_aux; [ eassumption | reflexivity | eassumption | ]. destructAll.
      do 2 eexists. split. econstructor 2. eassumption. intros; exact I.
      rewrite plus_assoc. reflexivity.
  Qed.

  Lemma bstep_OOT_monotonic_aux ex rho e r cin cout cin' c :
    bstep ex rho e cin r cout ->
    r = OOT ->
    cin = (c <+> cin') ->
    exists cout' c, bstep ex rho e cin' OOT cout' /\ cout = (c <+> cout').
  Proof.
    set (P := fun ex rho e cin (r : res) (cout : trace) =>
                forall c cin',
                  r = OOT ->
                  cin = (c <+> cin') ->
                  exists cout' c, bstep ex rho e cin' OOT cout' /\ cout = (c <+> cout')).
    set (P0 := fun ex rho e cin (r : res) (cout : trace) =>
                 forall c cin',
                   r = OOT ->
                   cin = (c <+> cin') ->
                   exists cout' c, bstep_fuel ex rho e cin' OOT cout' /\ cout = (c <+> cout')).
    intros Hstep. revert c cin'.
    induction Hstep using bstep_ind' with (P := P) (P0 := P0); unfold P, P0 in *;
      intros c' cin' Heq Hleq; subst;
      try now (edestruct IHHstep; eauto; destructAll; do 2 eexists; split;
               [ econstructor; eauto | reflexivity ]).
    - destruct (lt_all_dec cin' cin1) as [Hlt1 | [z Hz]].
      + edestruct bstep_fuel_lt_OOT as (cout' & c & Hs & Heq); [ eassumption | eassumption | ]. subst.
        exists cout', (c <+> cout2). split. eapply BStept_letapp_oot; eauto.
        rewrite !plus_assoc, (plus_comm cout' cout2). reflexivity.
      + subst cin'. rewrite <- plus_assoc, (plus_comm cin1) in Hleq.
        eapply plus_inv in Hleq. subst.
        edestruct IHHstep0 as (cout' & c & Hs & Heq); [ reflexivity | reflexivity | ]. subst.
        do 2 eexists. split. rewrite plus_comm. econstructor; eauto.
        rewrite <- plus_assoc. rewrite (plus_comm _ c). rewrite plus_assoc. reflexivity.
    - congruence.
    - do 2 eexists. split. econstructor 1. eapply plus_lt. rewrite plus_comm. eassumption.
      rewrite plus_zero. reflexivity.
    - edestruct (lt_all_dec cin' (one_w e)).
      + do 2 eexists. split.
        now econstructor; eauto. rewrite (plus_comm _ <0>). rewrite plus_zero. reflexivity.
      + destructAll. rewrite <- plus_assoc in Hleq. eapply plus_inv in Hleq. subst.
        edestruct IHHstep. reflexivity. reflexivity. destructAll.
        do 2 eexists. split. econstructor 2; [ eassumption | intros; exact I ].
        rewrite plus_assoc. reflexivity.
  Qed.

  Lemma bstep_fuel_OOT_monotonic ex rho e c1 c2 cout :
    bstep_fuel ex rho e (c1 <+> c2) OOT cout ->
    exists cout' c, bstep_fuel ex rho e c2 OOT cout' /\ cout = (c <+> cout').
  Proof.
    intros Hs; inv Hs.
    - do 2 eexists. split. econstructor 1. eapply plus_lt. rewrite plus_comm. eassumption.
      rewrite plus_zero. reflexivity.
    - edestruct (lt_all_dec c2 (one_w e)).
      + do 2 eexists. split.
        now econstructor; eauto. rewrite (plus_comm _ <0>). rewrite plus_zero. reflexivity.
      + destructAll. rewrite <- plus_assoc in H. eapply plus_inv in H. subst.
        edestruct bstep_OOT_monotonic_aux; [ eassumption | reflexivity | reflexivity |]. destructAll.
        do 2 eexists. split. econstructor 2; [ eassumption | intros; exact I ].
        rewrite plus_assoc. reflexivity.
  Qed.

  Lemma bstep_fuel_zero_OOT ex rho e :
    bstep_fuel ex rho e <0> OOT <0>.
  Proof. econstructor. eapply zero_one_lt. Qed.

End EVAL.
