(* Compatibility lemmas for the parameterized λweb relations.

   These are the λweb counterparts of the [preord_exp_*_compat] lemmas of
   LambdaANF/logical_relations.v.  They hold for any transformation-specific
   relation [VT]: constructors, projections, case analyses, function
   definitions and returns are handled generically, as are calls whose
   callee is related by [V_fun] (this covers exposed webs, and internal webs
   that a transformation leaves untouched). *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics algebra.
From CertiRocq.LambdaANF Require term term_util.
From CertiRocq.LambdaWeb Require Import syntax semantics exposed post.

Import ListNotations.

Open Scope alg_scope.

Section Compat.

  Variable (cenv : term.ctor_env).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Local Notation PostT := (@exposed.PostT fuel trace).
  Local Notation PostGT := (@exposed.PostGT fuel trace).
  Local Notation VTransT := (@exposed.VTransT fuel trace).

  Context (VT : VTransT) {HVT : VTransProps VT}.

  Context (P1 P2 : PostT) (PG : PostGT).

  Notation V := (V cenv VT PG).
  Notation E := (E cenv VT PG).
  Notation var_rel := (var_rel cenv VT PG).

  Lemma to_nat_one_w e : to_nat (one_w e) = 1.
  Proof. unfold one_w, algebra.one. eapply to_nat_one. Qed.

  Ltac fuel_arith :=
    repeat match goal with
           | [ H : context [ to_nat (_ <+> _) ] |- _ ] => rewrite to_nat_add in H
           | [ |- context [ to_nat (_ <+> _) ] ] => rewrite to_nat_add
           | [ H : context [ to_nat (one_w _) ] |- _ ] => rewrite to_nat_one_w in H
           | [ |- context [ to_nat (one_w _) ] ] => rewrite to_nat_one_w
           end; lia.

  Lemma R_exposed_ex k r1 r2 (ex : bool) :
    R cenv VT PG k r1 r2 -> (ex = true -> exposed_res r1) -> (ex = true -> exposed_res r2).
  Proof. intros HR Hex Heq. destruct (R_exposed cenv VT PG k r1 r2 HR) as [H1 _]. eauto. Qed.

  Lemma Forall2_V_exposed_imp k (w : web) vs1 vs2 :
    Forall2 (V k) vs1 vs2 ->
    (exposedb w = true -> Forall exposed_val vs1) ->
    (exposedb w = true -> Forall exposed_val vs2).
  Proof. intros Hall H Hw. eapply (proj1 (Forall2_V_exposed cenv VT PG k vs1 vs2 Hall)); eauto. Qed.

  (** * Constructors *)

  Lemma E_constr_compat ex k rho1 rho2 x x' w t ys1 ys2 e1 e2
        (Hcompat : post_constr_compat' x w t ys1 e1 rho1 x' w t ys2 e2 rho2 P1 P2)
        (HOOT : post_OOT' (Econstr x w t ys1 e1) rho1 (Econstr x' w t ys2 e2) rho2 P2) :
    Forall2 (var_rel k rho1 rho2) ys1 ys2 ->
    (forall m v1 v2,
        m < k ->
        V m v1 v2 ->
        E P1 ex m (e1, M.set x v1 rho1) (e2, M.set x' v2 rho2)) ->
    E P2 ex k (Econstr x w t ys1 e1, rho1) (Econstr x' w t ys2 e2, rho2).
  Proof.
    intros Hall Hk r1 cin cout Hleq Hstep. inv Hstep.
    - exists OOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H.
      edestruct var_rel_get_list as (vs2 & Hget2 & Hvs); eauto.
      edestruct (Hk (k - 1)) as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
        [ fuel_arith | | | eassumption | ].
      + eapply V_Vconstr; eauto. eapply V_mono_Forall2; eauto. lia.
      + fuel_arith.
      + do 3 eexists. split; [| split ].
        * econstructor 2; [ econstructor; eauto |].
          -- eapply Forall2_V_exposed_imp; eauto.
          -- eapply R_exposed_ex; eauto.
        * eapply Hcompat; eauto.
        * eapply R_mono; eauto. fuel_arith.
  Qed.

  (** The same, where the continuation knows the source value. *)
  Lemma E_constr_compat_vals ex k rho1 rho2 x x' w t ys1 ys2 e1 e2
        (Hcompat : post_constr_compat' x w t ys1 e1 rho1 x' w t ys2 e2 rho2 P1 P2)
        (HOOT : post_OOT' (Econstr x w t ys1 e1) rho1 (Econstr x' w t ys2 e2) rho2 P2) :
    Forall2 (var_rel k rho1 rho2) ys1 ys2 ->
    (forall m vs1 v2,
        m < k ->
        get_list ys1 rho1 = Some vs1 ->
        V m (Vconstr w t vs1) v2 ->
        E P1 ex m (e1, M.set x (Vconstr w t vs1) rho1) (e2, M.set x' v2 rho2)) ->
    E P2 ex k (Econstr x w t ys1 e1, rho1) (Econstr x' w t ys2 e2, rho2).
  Proof.
    intros Hall Hk r1 cin cout Hleq Hstep. inv Hstep.
    - exists OOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H.
      edestruct var_rel_get_list as (vs2 & Hget2 & Hvs); eauto.
      edestruct (Hk (k - 1)) as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
        [ fuel_arith | eassumption | | | eassumption | ].
      + eapply V_Vconstr; eauto. eapply V_mono_Forall2; eauto. lia.
      + fuel_arith.
      + do 3 eexists. split; [| split ].
        * econstructor 2; [ econstructor; eauto |].
          -- eapply Forall2_V_exposed_imp; eauto.
          -- eapply R_exposed_ex; eauto.
        * eapply Hcompat; eauto.
        * eapply R_mono; eauto. fuel_arith.
  Qed.

  (** * Projections *)

  Lemma E_proj_compat ex k rho1 rho2 x x' w t n y1 y2 e1 e2
        (Hcompat : post_proj_compat' x w t n y1 e1 rho1 x' w t n y2 e2 rho2 P1 P2)
        (HOOT : post_OOT' (Eproj x w t n y1 e1) rho1 (Eproj x' w t n y2 e2) rho2 P2) :
    var_rel k rho1 rho2 y1 y2 ->
    (forall m v1 v2,
        m < k ->
        V m v1 v2 ->
        E P1 ex m (e1, M.set x v1 rho1) (e2, M.set x' v2 rho2)) ->
    E P2 ex k (Eproj x w t n y1 e1, rho1) (Eproj x' w t n y2 e2, rho2).
  Proof.
    intros Hy Hk r1 cin cout Hleq Hstep. inv Hstep.
    - exists OOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H.
      edestruct Hy as (v2 & Hget2 & Hv); eauto.
      edestruct V_Vconstr_l as (vs2 & Heq & Hvs); eauto. subst.
      match goal with [ Hn : nthN _ _ = Some _ |- _ ] => destruct (Forall2_nthN _ _ _ _ _ Hvs Hn) as (v2' & Hnth2 & Hv') end.
      edestruct (Hk (k - 1)) as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
        [ fuel_arith | | | eassumption | ].
      + eapply V_mono; eauto. lia.
      + fuel_arith.
      + do 3 eexists. split; [| split ].
        * econstructor 2; [ econstructor; eauto |].
          eapply R_exposed_ex; eauto.
        * eapply Hcompat; eauto.
        * eapply R_mono; eauto. fuel_arith.
  Qed.

  (** * Case analysis *)

  Lemma E_case_nil_compat ex k rho1 rho2 x1 x2 w
        (HOOT : post_OOT' (Ecase x1 w []) rho1 (Ecase x2 w []) rho2 P2) :
    E P2 ex k (Ecase x1 w [], rho1) (Ecase x2 w [], rho2).
  Proof.
    intros r1 cin cout Hleq Hstep. inv Hstep.
    - exists OOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H. match goal with [ Hft : find_tag_nth [] _ _ _ |- _ ] => inv Hft end.
  Qed.

  Lemma erase_branches_same_tags (D1 D2 : list (ctor_tag * exp)) :
    Forall2 (fun p p' => fst p = fst p') D1 D2 ->
    Forall2 (fun p p' => fst p = fst p') (erase_branches D1) (erase_branches D2).
  Proof.
    intros H; induction H; simpl; constructor; eauto.
    destruct x, y; simpl in *; eauto.
  Qed.

  Lemma E_case_cons_compat ex k rho1 rho2 x1 x2 w c e1 e2 D1 D2
        (Hcompat_hd : post_case_compat_hd' x1 w c e1 D1 rho1 x2 w c e2 D2 rho2 P1 P2)
        (Hcompat_tl : post_case_compat_tl' x1 w c e1 D1 rho1 x2 w c e2 D2 rho2 P2 P2)
        (HOOT : post_OOT' (Ecase x1 w ((c, e1) :: D1)) rho1 (Ecase x2 w ((c, e2) :: D2)) rho2 P2) :
    Forall2 (fun p p' => fst p = fst p') D1 D2 ->
    var_rel k rho1 rho2 x1 x2 ->
    (forall m, m < k -> E P1 ex m (e1, rho1) (e2, rho2)) ->
    E P2 ex k (Ecase x1 w D1, rho1) (Ecase x2 w D2, rho2) ->
    E P2 ex k (Ecase x1 w ((c, e1) :: D1), rho1) (Ecase x2 w ((c, e2) :: D2), rho2).
  Proof.
    intros Hall Henv Hexp_hd Hexp_tl r1 cin cout Hleq Hstep. inv Hstep.
    - exists OOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H.
      edestruct Henv as (v2 & Hget2 & Hv); eauto.
      edestruct V_Vconstr_l as (vs2 & Heq & Hvs); eauto. subst.
      assert (Hcc : term_util.caseConsistent cenv (erase_branches ((c, e2) :: D2)) t).
      { eapply term_util.caseConsistent_same_ctor_tags; [| eassumption ].
        eapply erase_branches_same_tags. constructor; eauto. }
      match goal with [ Hft : find_tag_nth ((_, _) :: _) _ _ _ |- _ ] => inv Hft end.
      + edestruct (Hexp_hd (k - 1)) as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
          [ fuel_arith | | eassumption | ]; [ fuel_arith | ].
        do 3 eexists. split; [| split ].
        * econstructor 2; [ econstructor; eauto; constructor |].
          eapply R_exposed_ex; eauto.
        * eapply Hcompat_hd; eauto.
        * eapply R_mono; eauto. fuel_arith.
      + assert (Hcc1 : term_util.caseConsistent cenv (erase_branches D1) t).
        { match goal with
          | [ Hc : term_util.caseConsistent _ (erase_branches ((_, _) :: _)) _ |- _ ] =>
              simpl in Hc; inv Hc; eassumption
          end. }
        edestruct Hexp_tl as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
          [ | econstructor 2; [ econstructor; eassumption | eassumption ] | ].
        * fuel_arith.
        * inv Hstep2.
          -- destruct r1; try contradiction.
             exists OOT, cin', <0>. split; [| split ].
             ++ econstructor 1. eassumption.
             ++ eapply Hcompat_tl. eassumption.
             ++ exact I.
          -- match goal with [ Hb : bstep _ _ _ (Ecase _ _ _) _ _ _ |- _ ] => inv Hb end.
             repeat subst_exp.
             do 3 eexists. split; [| split ].
             ++ econstructor 2; [| eassumption ].
                econstructor; eauto. constructor; eauto.
             ++ eapply Hcompat_tl. eassumption.
             ++ eassumption.
  Qed.

  (** * Returns *)

  Lemma E_halt_compat ex k rho1 rho2 x1 x2
        (HOOT : post_OOT' (Ehalt x1) rho1 (Ehalt x2) rho2 P2)
        (Hbase : post_base' x1 rho1 x2 rho2 P2) :
    var_rel k rho1 rho2 x1 x2 ->
    E P2 ex k (Ehalt x1, rho1) (Ehalt x2, rho2).
  Proof.
    intros Hvar r1 cin cout Hleq Hstep. inv Hstep.
    - exists OOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H. edestruct Hvar as (v2 & Hget2 & Hv); eauto.
      do 3 eexists. split; [| split ].
      + econstructor 2; [ econstructor; eauto |].
        eapply (R_exposed_ex k (Res v) (Res v2)); eauto.
      + rewrite !plus_zero. eapply Hbase.
      + simpl. eapply V_mono; eauto. lia.
  Qed.

  (** * Stuck forms (primitives are not given a semantics in λANF) *)

  Lemma lt_one_w (c : fuel) e1 e2 : c << one_w e1 -> c << one_w e2.
  Proof.
    unfold one_w, algebra.one.
    rewrite (one_eq (exp_to_fin (erase e2)) (exp_to_fin (erase e1))). auto.
  Qed.

  Lemma E_stuck_compat ex k rho1 rho2 e1 e2
        (HOOT : post_OOT' e1 rho1 e2 rho2 P2) :
    (forall c r cout, ~ bstep cenv ex rho1 e1 c r cout) ->
    E P2 ex k (e1, rho1) (e2, rho2).
  Proof.
    intros Hstuck r1 cin cout Hleq Hstep. inv Hstep.
    - exists OOT, cin, <0>. split; [ constructor; eapply lt_one_w; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - exfalso; eapply Hstuck; eauto.
  Qed.

  Lemma Eprim_val_stuck ex rho x p e c r cout : ~ bstep cenv ex rho (Eprim_val x p e) c r cout.
  Proof. intros H; inv H. Qed.

  Lemma Eprim_stuck ex rho x p ys e c r cout : ~ bstep cenv ex rho (Eprim x p ys e) c r cout.
  Proof. intros H; inv H. Qed.

  (** * Function definitions *)

  Lemma E_fun_compat ex k rho1 rho2 B1 B2 e1 e2
        (HOOT : post_OOT' (Efun B1 e1) rho1 (Efun B2 e2) rho2 P2)
        (Hcompat : post_fun_compat' B1 e1 rho1 B2 e2 rho2 P1 P2) :
    E P1 ex (k - 1) (e1, def_funs B1 B1 rho1 rho1) (e2, def_funs B2 B2 rho2 rho2) ->
    E P2 ex k (Efun B1 e1, rho1) (Efun B2 e2, rho2).
  Proof.
    intros Hexp r1 cin cout Hleq Hstep. inv Hstep.
    - exists OOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H.
      edestruct Hexp as (r2 & cin' & cout' & Hstep2 & Hpost & HR); [| eassumption |]. fuel_arith.
      do 3 eexists. split; [| split ].
      + econstructor 2; [ econstructor; eauto |]. eapply R_exposed_ex; eauto.
      + eapply Hcompat; eauto.
      + eapply R_mono; eauto. fuel_arith.
  Qed.

  (** Building the relation for a closure that keeps its calling
      convention from the relation of its body. *)
  Lemma V_fun_def k rho1 rho2 B1 B2 f1 f2 w xs1 xs2 e1 e2 :
    find_def f1 B1 = Some (w, xs1, e1) ->
    find_def f2 B2 = Some (w, xs2, e2) ->
    length xs1 = length xs2 ->
    (forall j vs1 vs2 rho1' rho2',
        j < k ->
        (exposedb w = true -> Forall exposed_val vs1) ->
        Forall2 (V j) vs1 vs2 ->
        set_lists xs1 vs1 (def_funs B1 B1 rho1 rho1) = Some rho1' ->
        set_lists xs2 vs2 (def_funs B2 B2 rho2 rho2) = Some rho2' ->
        E PG (exposedb w) j (e1, rho1') (e2, rho2')) ->
    V_fun cenv PG V k (Vfun rho1 B1 f1) (Vfun rho2 B2 f2).
  Proof.
    intros Hf1 Hf2 Hlen Hbody vs1 vs2 j w' xs1' e1' rho1' Hlenv Hf1' Hset1.
    rewrite Hf1 in Hf1'. inv Hf1'.
    symmetry in Hset1.
    edestruct (set_lists_length3 (def_funs B2 B2 rho2 rho2) xs2 vs2) as [rho2' Hset2].
    { pose proof (set_lists_length_eq _ _ _ _ Hset1) as Hl. rewrite <- Hlenv. etransitivity; [ symmetry; exact Hlen | exact Hl ]. }
    do 3 eexists. split; [ eassumption | split; [ symmetry; eassumption |] ].
    intros Hlt Hexp Hall. eapply Hbody; eauto.
  Qed.

  (** * Calls *)

  (** The callee must be related by [V_fun] whenever its web is the web of
      the call.  This holds for exposed webs ([var_rel_exposed_fun]) and
      for webs whose closures a transformation leaves untouched. *)
  Definition fun_rel k rho1 rho2 f1 f2 (w : web) :=
    forall v1, M.get f1 rho1 = Some v1 ->
               exists v2, M.get f2 rho2 = Some v2 /\
                          (val_web v1 = Some w -> V_fun cenv PG V k v1 v2).

  Lemma var_rel_exposed_fun k rho1 rho2 f1 f2 w :
    exposedb w = true -> var_rel k rho1 rho2 f1 f2 -> fun_rel k rho1 rho2 f1 f2 w.
  Proof.
    intros Hw Hvar v1 Hget. edestruct Hvar as (v2 & Hget2 & Hv); eauto.
    eexists; split; eauto. intros Hweb. destruct v1; simpl in Hweb; try congruence.
    eapply V_exposed_fun; eauto.
  Qed.

  Lemma fun_rel_mono k j rho1 rho2 f1 f2 w :
    fun_rel k rho1 rho2 f1 f2 w -> j <= k -> fun_rel j rho1 rho2 f1 f2 w.
  Proof.
    intros H Hleq v1 Hget. edestruct H as (v2 & Hget2 & Hv); eauto.
    eexists; split; eauto. intros Hw. eapply V_fun_mono; eauto.
  Qed.

  Lemma E_app_compat ex k rho1 rho2 f1 f2 w ys1 ys2
        (Hcompat : post_app_compat' f1 w ys1 rho1 f2 w ys2 rho2 P2 PG)
        (HOOT : post_OOT' (Eapp f1 w ys1) rho1 (Eapp f2 w ys2) rho2 P2) :
    fun_rel k rho1 rho2 f1 f2 w ->
    Forall2 (var_rel k rho1 rho2) ys1 ys2 ->
    E P2 ex k (Eapp f1 w ys1, rho1) (Eapp f2 w ys2, rho2).
  Proof.
    intros Hfun Hall r1 cin cout Hleq Hstep. inv Hstep.
    - exists OOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H.
      edestruct Hfun as (v2 & Hget2 & Hv); eauto.
      specialize (Hv ltac:(simpl; unfold fun_web; match goal with [ Hfd : find_def _ _ = Some _ |- _ ] => rewrite Hfd end; reflexivity)).
      edestruct var_rel_get_list as (vs2 & Hgetl2 & Hvs); eauto.
      destruct v2; try contradiction.
      edestruct (Hv vs vs2 (k - 1)) as (xs2 & e2 & rho2' & Hf2 & Hset2 & Hbody); eauto.
      + eapply Forall2_length; eauto.
      + edestruct Hbody as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
          [ fuel_arith | eassumption | | | eassumption | ].
        * eapply V_mono_Forall2; eauto. lia.
        * fuel_arith.
        * do 3 eexists. split; [| split ].
          -- econstructor 2; [ econstructor; eauto |].
             ++ eapply Forall2_V_exposed_imp; eauto.
             ++ eapply R_exposed_ex; eauto.
          -- eapply Hcompat; eauto.
          -- eapply R_mono; eauto. fuel_arith.
  Qed.

  Lemma E_letapp_compat ex k rho1 rho2 x x' f1 f2 w ys1 ys2 e1 e2
        (Hcompat : post_letapp_compat' cenv x f1 w ys1 e1 rho1 x' f2 w ys2 e2 rho2 P1 P2 PG)
        (HcompatOOT : post_letapp_compat_OOT' x f1 w ys1 e1 rho1 x' f2 w ys2 e2 rho2 P2 PG)
        (HOOT : post_OOT' (Eletapp x f1 w ys1 e1) rho1 (Eletapp x' f2 w ys2 e2) rho2 P2) :
    fun_rel k rho1 rho2 f1 f2 w ->
    Forall2 (var_rel k rho1 rho2) ys1 ys2 ->
    (forall m v1 v2,
        m < k ->
        (exposedb w = true -> exposed_val v1) ->
        V m v1 v2 ->
        E P1 ex m (e1, M.set x v1 rho1) (e2, M.set x' v2 rho2)) ->
    E P2 ex k (Eletapp x f1 w ys1 e1, rho1) (Eletapp x' f2 w ys2 e2, rho2).
  Proof.
    intros Hfun Hall Hk r1 cin cout Hleq Hstep. inv Hstep.
    - exists OOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H.
      + (* the call returns *)
        edestruct Hfun as (v2 & Hget2 & Hv); eauto.
        specialize (Hv ltac:(simpl; unfold fun_web; match goal with [ Hfd : find_def _ _ = Some _ |- _ ] => rewrite Hfd end; reflexivity)).
        edestruct var_rel_get_list as (vs2 & Hgetl2 & Hvs); eauto.
        destruct v2; try contradiction.
        edestruct (Hv vs vs2 (k - 1)) as (xs2 & eb2 & rho2' & Hf2 & Hset2 & Hbody); eauto.
        { eapply Forall2_length; eauto. }
        edestruct Hbody as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
          [ fuel_arith | eassumption | | | eassumption | ].
        * eapply V_mono_Forall2; eauto. lia.
        * fuel_arith.
        * destruct r2 as [| v2]; try contradiction. simpl in HR.
          edestruct (Hk (k - 1 - to_nat cin1)) as (r2 & cin'' & cout'' & Hstep3 & Hpost' & HR');
            [ fuel_arith | | eassumption | | eassumption | ]; [ eapply bstep_fuel_exposedb; eassumption | fuel_arith | ].
          do 3 eexists. split; [| split ].
          -- econstructor 2; [ econstructor; eauto |].
             ++ eapply Forall2_V_exposed_imp; eauto.
             ++ eapply R_exposed_ex; eauto.
          -- eapply Hcompat; eauto.
          -- eapply R_mono; eauto. fuel_arith.
      + (* the call runs out of fuel *)
        edestruct Hfun as (v2 & Hget2 & Hv); eauto.
        specialize (Hv ltac:(simpl; unfold fun_web; match goal with [ Hfd : find_def _ _ = Some _ |- _ ] => rewrite Hfd end; reflexivity)).
        edestruct var_rel_get_list as (vs2 & Hgetl2 & Hvs); eauto.
        destruct v2; try contradiction.
        edestruct (Hv vs vs2 (k - 1)) as (xs2 & eb2 & rho2' & Hf2 & Hset2 & Hbody); eauto.
        { eapply Forall2_length; eauto. }
        edestruct Hbody as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
          [ fuel_arith | eassumption | | | eassumption | ].
        * eapply V_mono_Forall2; eauto. lia.
        * fuel_arith.
        * destruct r2; try contradiction.
          do 3 eexists. split; [| split ].
          -- econstructor 2; [ eapply BStept_letapp_oot; eauto |].
             ++ eapply Forall2_V_exposed_imp; eauto.
             ++ intros; exact I.
          -- eapply HcompatOOT; eauto.
          -- exact I.
  Qed.

End Compat.
