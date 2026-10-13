(* The annotation relation: from λANF to λweb (Section 7.2 and Fig. 10 of
   the paper).

   There is no flow analysis yet: we only fix the correctness criterion an
   analysis must meet.  The relation is cross-language, λANF on the left
   and λweb on the right, and only relates exposed λweb values: whatever the
   analysis does internally, the values it exports (and imports) must be
   exposed and follow a fixed interface, so that separately annotated units
   can be linked:

   - exposed functions keep their λANF function tag as their web (λANF
     already uses its function tags as calling conventions, e.g. one per
     arity);
   - exposed constructors carry the fixed web [w_con].

   We prove that the relation implies behavioral refinement (Lemma 7.3) and
   is compatible with linking (Lemma 7.4). *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics algebra set_util.
From CertiRocq.LambdaANF Require term term_util identifiers.
From CertiRocq.LambdaANF Require eval rel_comp.
From CertiRocq.LambdaWeb Require Import syntax semantics exposed post compat comp erase.

Import ListNotations.

Open Scope alg_scope.

Section Anno.

  Variable (cenv : term.ctor_env).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Local Notation PostT := (@exposed.PostT fuel trace).
  Local Notation PostGT := (@exposed.PostGT fuel trace).
  Local Notation VTransT := (@exposed.VTransT fuel trace).

  (** The web of exposed constructors *)
  Variable (w_con : web).
  Hypothesis (Hw_con : exposedb w_con = true).

  Definition PostT_a : Type := (term.exp * aenv * fuel * trace) -> (exp * env * fuel * trace) -> Prop.

  Definition R_a' (V : nat -> aval -> val -> Prop) (k : nat) (r1 : ares) (r2 : res) : Prop :=
    match r1, r2 with
    | CertiRocq.LambdaANF.eval.OOT, OOT => True
    | CertiRocq.LambdaANF.eval.Res v1, Res v2 => V k v1 v2
    | _, _ => False
    end.

  Definition E_a' (V : nat -> aval -> val -> Prop) (P : PostT_a) (k : nat)
             (p1 : term.exp * aenv) (p2 : exp * env) : Prop :=
    let '(e1, rho1) := p1 in
    let '(e2, rho2) := p2 in
    forall r1 cin cout,
      to_nat cin <= k ->
      abstep_fuel cenv rho1 e1 cin r1 cout ->
      exists r2 cin' cout',
        bstep_fuel cenv true rho2 e2 cin' r2 cout' /\
        P (e1, rho1, cin, cout) (e2, rho2, cin', cout') /\
        R_a' V (k - to_nat cin) r1 r2.

  Definition V_a_fun (PG : PostT_a) (V' : nat -> aval -> val -> Prop) (k : nat) (v1 : aval) (v2 : val) : Prop :=
    match v1, v2 with
    | term.Vfun rho1 B1 f1, Vfun rho2 B2 f2 =>
        forall vs1 vs2 j t xs1 e1 rho1',
          length vs1 = length vs2 ->
          term.find_def f1 B1 = Some (t, xs1, e1) ->
          Some rho1' = set_lists xs1 vs1 (term.def_funs B1 B1 rho1 rho1) ->
          exists xs2 e2 rho2',
            find_def f2 B2 = Some (t, xs2, e2) /\
            Some rho2' = set_lists xs2 vs2 (def_funs B2 B2 rho2 rho2) /\
            (j < k -> Forall2 (V' j) vs1 vs2 -> E_a' V' PG j (e1, rho1') (e2, rho2'))
    | _, _ => False
    end.

  Fixpoint V_a (PG : PostT_a) (k : nat) (v1 : aval) (v2 : val) {struct k} : Prop :=
    let V' : nat -> aval -> val -> Prop :=
      match k with
      | 0 => fun _ _ _ => False
      | S k0 => fun j => V_a PG (k0 - (k0 - j))
      end in
    let fix Vi (v1 : aval) (v2 : val) {struct v1} : Prop :=
      let fix Forall2_aux vs1 vs2 :=
        match vs1, vs2 with
        | [], [] => True
        | v1 :: vs1, v2 :: vs2 => Vi v1 v2 /\ Forall2_aux vs1 vs2
        | _, _ => False
        end in
      wf_val v2 /\ exposed_val v2 /\
      match v1, v2 with
      | term.Vconstr c1 vs1, Vconstr w c2 vs2 => w = w_con /\ c1 = c2 /\ Forall2_aux vs1 vs2
      | term.Vfun _ _ _, _ => V_a_fun PG V' k v1 v2
      | term.Vprim p1, Vprim p2 => p1 = p2
      | term.Vint z1, Vint z2 => z1 = z2
      | _, _ => False
      end
    in Vi v1 v2.

  Definition V_a_ (PG : PostT_a) (k : nat) (v1 : aval) (v2 : val) : Prop :=
    wf_val v2 /\ exposed_val v2 /\
    match v1, v2 with
    | term.Vconstr c1 vs1, Vconstr w c2 vs2 => w = w_con /\ c1 = c2 /\ Forall2 (V_a PG k) vs1 vs2
    | term.Vfun _ _ _, _ => V_a_fun PG (V_a PG) k v1 v2
    | term.Vprim p1, Vprim p2 => p1 = p2
    | term.Vint z1, Vint z2 => z1 = z2
    | _, _ => False
    end.

  Lemma E_a'_ext V1 V2 P k p1 p2 :
    (forall j, j <= k -> forall v1 v2, V1 j v1 v2 <-> V2 j v1 v2) ->
    E_a' V1 P k p1 p2 -> E_a' V2 P k p1 p2.
  Proof.
    destruct p1 as [e1 rho1], p2 as [e2 rho2]. simpl.
    intros Hext HE r1 cin cout Hleq Hstep.
    edestruct HE as (r2 & cin' & cout' & Hstep' & HP & HR); eauto.
    do 3 eexists; split; [ eassumption | split; [ eassumption |] ].
    destruct r1, r2; simpl in *; eauto. eapply Hext; eauto. lia.
  Qed.

  Lemma V_a_fun_ext PG V1 V2 k v1 v2 :
    (forall j, j < k -> forall v1 v2, V1 j v1 v2 <-> V2 j v1 v2) ->
    V_a_fun PG V1 k v1 v2 -> V_a_fun PG V2 k v1 v2.
  Proof.
    destruct v1, v2; cbn -[E_a']; try easy.
    intros Hext Hfn vs1 vs2 j ft xs1 e1 rho1' Hlen Hfind Hset.
    edestruct (Hfn vs1 vs2 j ft xs1 e1 rho1' Hlen Hfind Hset) as (xs2 & e2 & rho2' & Hfind2 & Hset2 & Hbody).
    do 3 eexists. split; [ eassumption | split; [ eassumption |] ].
    intros Hlt Hall. eapply E_a'_ext; [| eapply Hbody; eauto ].
    - intros. eapply Hext. lia.
    - eapply Forall2_monotonic; [| eassumption ]. intros. eapply Hext; eauto.
  Qed.

  Lemma V_a_fun_mono PG V k j v1 v2 : V_a_fun PG V k v1 v2 -> j <= k -> V_a_fun PG V j v1 v2.
  Proof.
    destruct v1, v2; cbn -[E_a']; try easy.
    intros Hfn Hleq vs1 vs2 i ft xs1 e1 rho1' Hlen Hfind Hset.
    edestruct (Hfn vs1 vs2 i ft xs1 e1 rho1' Hlen Hfind Hset) as (xs2 & e2 & rho2' & Hfind2 & Hset2 & Hbody).
    do 3 eexists. split; [ eassumption | split; [ eassumption |] ].
    intros Hlt. eapply Hbody. lia.
  Qed.

  Lemma aval_ind_Forall (P : aval -> Prop) :
    (forall c vs, Forall P vs -> P (term.Vconstr c vs)) ->
    (forall rho B f, P (term.Vfun rho B f)) ->
    (forall p, P (term.Vprim p)) ->
    (forall z, P (term.Vint z)) ->
    forall v, P v.
  Proof.
    intros H1 H2 H3 H4. fix IH 1. destruct v as [c vs | rho B f | p | z].
    - apply H1. induction vs as [| v vs IHvs]; constructor; [ apply IH | apply IHvs ].
    - apply H2.
    - apply H3.
    - apply H4.
  Qed.

  Lemma V_a_eq PG k v1 v2 : V_a PG k v1 v2 <-> V_a_ PG k v1 v2.
  Proof.
    revert v2. induction v1 using aval_ind_Forall; intros v2;
      unfold V_a_; destruct k as [| k0]; cbn -[V_a_fun]; try reflexivity.
    - destruct v2; try reflexivity. rewrite Forall2_aux_eq. reflexivity.
    - destruct v2; try reflexivity. rewrite Forall2_aux_eq. reflexivity.
    - split; intros (H1 & H2 & H3); repeat (split; [ eassumption |]); eapply V_a_fun_ext; eauto; intros; lia.
    - split; intros (H1 & H2 & H3); repeat (split; [ eassumption |]); eapply V_a_fun_ext; eauto;
        intros j Hj; cbv beta; replace (k0 - (k0 - j)) with j by lia; reflexivity.
  Qed.

  Global Opaque V_a.

  Lemma V_a_mono PG k : forall j v1 v2, V_a PG k v1 v2 -> j <= k -> V_a PG j v1 v2.
  Proof.
    intros j v1. revert j. induction v1 using aval_ind_Forall; intros j v2 Hv Hleq;
      rewrite V_a_eq in *; unfold V_a_ in *; destructAll; repeat (split; [ eassumption |]).
    - destruct v2; try contradiction. destructAll. split; eauto. split; eauto.
      match goal with [ Ha : Forall2 _ vs ?l |- _ ] => clear -H Ha Hleq; revert l Ha end.
      induction H; intros l2 Hall; inv Hall; constructor; eauto.
    - eapply V_a_fun_mono; eauto.
    - eauto.
    - eauto.
  Qed.

  Lemma R_a_mono PG k j r1 r2 : R_a' (V_a PG) k r1 r2 -> j <= k -> R_a' (V_a PG) j r1 r2.
  Proof. destruct r1, r2; simpl; eauto. intros. eapply V_a_mono; eauto. Qed.

  Definition E_a PG P k p1 p2 := E_a' (V_a PG) P k p1 p2.

  Lemma V_a_exposed PG k v1 v2 : V_a PG k v1 v2 -> exposed_val v2.
  Proof. rewrite V_a_eq. intros H; apply H. Qed.

  Lemma V_a_wf PG k v1 v2 : V_a PG k v1 v2 -> wf_val v2.
  Proof. rewrite V_a_eq. intros H; apply H. Qed.

  (** ** Environments *)

  Definition var_rel_a PG k (rho1 : aenv) (rho2 : env) x y : Prop :=
    forall v1, M.get x rho1 = Some v1 -> exists v2, M.get y rho2 = Some v2 /\ V_a PG k v1 v2.

  Definition G_a PG k (S : Ensemble var) (rho1 : aenv) (rho2 : env) : Prop :=
    wf_env rho2 /\ forall x, S x -> var_rel_a PG k rho1 rho2 x x.

  Lemma G_a_mono PG k j S rho1 rho2 : G_a PG k S rho1 rho2 -> j <= k -> G_a PG j S rho1 rho2.
  Proof.
    intros [Hwf HG] Hleq. split; eauto. intros x Hx v1 Hget. edestruct HG as (v2 & Hget2 & Hv); eauto.
    eexists; split; eauto. eapply V_a_mono; eauto.
  Qed.

  Lemma E_a_post_mono PG (P1 P2 : PostT_a) k p1 p2 :
    (forall c1 c2, P1 c1 c2 -> P2 c1 c2) -> E_a PG P1 k p1 p2 -> E_a PG P2 k p1 p2.
  Proof.
    destruct p1 as [e1 rho1], p2 as [e2 rho2]. unfold E_a, E_a'.
    intros Hinc HE r1 cin cout Hleq Hstep.
    edestruct HE as (r2 & cin' & cout' & Hstep' & HP & HR); eauto.
    do 3 eexists; split; [ eassumption | split; [ eapply Hinc; eassumption | eassumption ] ].
  Qed.

  (** ** Top level *)

  Definition E_anno_top (P : PostT_a) (PG : PostT_a) (e1 : term.exp) (e2 : exp) : Prop :=
    occurs_free e2 \subset identifiers.occurs_free e1 /\
    forall k rho1 rho2,
      G_a PG k (identifiers.occurs_free e1) rho1 rho2 ->
      term_util.binding_in_map (identifiers.occurs_free e1) rho1 ->
      E_a PG P k (e1, rho1) (e2, rho2).

  (** ** Adequacy *)

  Fixpoint value_ref_a' (v1 : aval) (v2 : val) : Prop :=
    let fix Forall2_aux vs1 vs2 :=
      match vs1, vs2 with
      | [], [] => True
      | v1 :: vs1, v2 :: vs2 => value_ref_a' v1 v2 /\ Forall2_aux vs1 vs2
      | _, _ => False
      end in
    match v1, v2 with
    | term.Vconstr c1 vs1, Vconstr _ c2 vs2 => c1 = c2 /\ Forall2_aux vs1 vs2
    | term.Vfun _ _ _, Vfun _ _ _ => True
    | term.Vint i1, Vint i2 => i1 = i2
    | term.Vprim p1, Vprim p2 => p1 = p2
    | _, _ => False
    end.

  Lemma V_a_value_ref PG k v1 v2 : V_a PG k v1 v2 -> value_ref_a' v1 v2.
  Proof.
    revert v2. induction v1 using aval_ind_Forall; intros v2 Hv;
      rewrite V_a_eq in Hv; unfold V_a_ in Hv; destructAll.
    - destruct v2; try contradiction. destructAll. simpl. split; eauto.
      match goal with [ Ha : Forall2 _ vs ?l |- _ ] => clear -H Ha; revert l Ha end.
      induction H as [| v vs Hv Hvs IHvs]; intros l2 Hall; inv Hall; simpl;
        [ exact I | split; [ eapply Hv; eassumption | eapply IHvs; eassumption ] ].
    - destruct v2; simpl in *; try contradiction; eauto.
    - destruct v2; try contradiction. simpl; eauto.
    - destruct v2; try contradiction. simpl; eauto.
  Qed.

  Definition aemp : aenv := M.empty aval.

  Definition refines_a (vref : aval -> val -> Prop) (e1 : term.exp) (e2 : exp) :=
    (forall v1 c1 t1,
        abstep_fuel cenv aemp e1 c1 (aRes v1) t1 ->
        exists v2 c2 t2, bstep_fuel cenv true emp e2 c2 (Res v2) t2 /\ vref v1 v2) /\
    (CertiRocq.LambdaANF.eval.diverge cenv aemp e1 -> diverge cenv true emp e2).

  Definition post_a_upper_bound (P : PostT_a) :=
    forall e1 rho1 e2 rho2,
    exists (f : fuel -> fuel),
    forall cin1 cin2 cout1 cout2,
      P (e1, rho1, f cin1, cout1) (e2, rho2, cin2, cout2) ->
      exists (c : fuel), cin2 = (c <+> cin1).

  (** Lemma 7.3: adequacy of annotation *)
  Theorem E_anno_refines P PG (HP : post_a_upper_bound P) e1 e2 :
    identifiers.closed_exp e1 -> E_anno_top P PG e1 e2 -> refines_a value_ref_a' e1 e2.
  Proof.
    intros Hc [_ Hrel]. split.
    - intros v1 c1 t1 Hs.
      edestruct (Hrel (to_nat c1) aemp emp) as (r2 & c2 & t2 & Hs2 & Hpost & HR);
        [ split; [ eapply wf_env_empty | intros x Hx; eapply Hc in Hx; inv Hx ]
        | intros x Hx; eapply Hc in Hx; inv Hx | | eassumption | ].
      + reflexivity.
      + destruct r2 as [| v2]; try contradiction.
        do 3 eexists. split; eauto. eapply V_a_value_ref; eauto.
    - intros Hdiv c2.
      destruct (HP e1 aemp e2 emp) as [f Hfn].
      destruct (Hdiv (f c2)) as [t1 Hs].
      edestruct (Hrel (to_nat (f c2)) aemp emp) as (r2 & c2' & t2 & Hs2 & Hpost & HR);
        [ split; [ eapply wf_env_empty | intros x Hx; eapply Hc in Hx; inv Hx ]
        | intros x Hx; eapply Hc in Hx; inv Hx | reflexivity | eassumption | ].
      destruct r2; try contradiction.
      edestruct Hfn as [c Heq]; eauto. subst.
      edestruct bstep_fuel_OOT_monotonic as (t2' & c' & Hs2' & _); eauto.
  Qed.

  (** ** Linking *)

  Definition post_a_fun (P1 P2 : PostT_a) :=
    forall B1 e1 rho1 B2 e2 rho2 c1 c2 cout1 cout2,
      P1 (e1, term.def_funs B1 B1 rho1 rho1, c1, cout1) (e2, def_funs B2 B2 rho2 rho2, c2, cout2) ->
      P2 (term.Efun B1 e1, rho1, c1 <+> one (term.Efun B1 e1), cout1 <+> one (term.Efun B1 e1))
         (Efun B2 e2, rho2, c2 <+> one_w (Efun B2 e2), cout2 <+> one_w (Efun B2 e2)).

  Definition post_a_OOT (P1 : PostT_a) :=
    forall e1 rho1 e2 rho2 c,
      c << one e1 -> P1 (e1, rho1, c, <0>) (e2, rho2, c, <0>).

  Definition post_a_letapp (P1 P2 PG : PostT_a) :=
    forall x f1 f2 t ys1 ys2 e1 rho1 e2 rho2 xs e_b1 v1 e_b2 v2
           rhoc1 rhoc2 B h vs rhoc1' c1 c1' c2 c2' cout1 cout2 cout1' cout2',
      M.get f1 rho1 = Some (term.Vfun rhoc1 B h) ->
      get_list ys1 rho1 = Some vs ->
      term.find_def h B = Some (t, xs, e_b1) ->
      set_lists xs vs (term.def_funs B B rhoc1 rhoc1) = Some rhoc1' ->
      abstep_fuel cenv rhoc1' e_b1 c1 (aRes v1) cout1 ->
      PG (e_b1, rhoc1', c1, cout1) (e_b2, rhoc2, c2, cout2) ->
      P1 (e1, M.set x v1 rho1, c1', cout1') (e2, M.set x v2 rho2, c2', cout2') ->
      P2 (term.Eletapp x f1 t ys1 e1, rho1, c1 <+> c1' <+> one (term.Eletapp x f1 t ys1 e1), cout1 <+> cout1' <+> one (term.Eletapp x f1 t ys1 e1))
         (Eletapp x f2 t ys2 e2, rho2, c2 <+> c2' <+> one_w (Eletapp x f2 t ys2 e2), cout2 <+> cout2' <+> one_w (Eletapp x f2 t ys2 e2)).

  Definition post_a_letapp_OOT (P2 PG : PostT_a) :=
    forall x f1 f2 t ys1 ys2 e1 rho1 e2 rho2 xs e_b1 e_b2 rhoc1 rhoc2 B h vs rhoc1' c1 c2 cout1 cout2,
      M.get f1 rho1 = Some (term.Vfun rhoc1 B h) ->
      get_list ys1 rho1 = Some vs ->
      term.find_def h B = Some (t, xs, e_b1) ->
      set_lists xs vs (term.def_funs B B rhoc1 rhoc1) = Some rhoc1' ->
      PG (e_b1, rhoc1', c1, cout1) (e_b2, rhoc2, c2, cout2) ->
      P2 (term.Eletapp x f1 t ys1 e1, rho1, c1 <+> one (term.Eletapp x f1 t ys1 e1), cout1 <+> one (term.Eletapp x f1 t ys1 e1))
         (Eletapp x f2 t ys2 e2, rho2, c2 <+> one_w (Eletapp x f2 t ys2 e2), cout2 <+> one_w (Eletapp x f2 t ys2 e2)).

  Class Post_properties_a (P PG : PostT_a) : Prop :=
    { HPa_fun : post_a_fun P P;
      HPa_letapp : post_a_letapp P P PG;
      HPa_letapp_OOT : post_a_letapp_OOT P PG;
      HPa_OOT : post_a_OOT P;
      HPa_GPost : forall c1 c2, P c1 c2 -> PG c1 c2 }.

  Lemma to_nat_one_a (e : term.exp) : to_nat (algebra.one e : fuel) = 1.
  Proof. unfold algebra.one. eapply to_nat_one. Qed.

  Ltac fuel_arith :=
    repeat match goal with
           | [ H : context [ to_nat (_ <+> _) ] |- _ ] => rewrite to_nat_add in H
           | [ |- context [ to_nat (_ <+> _) ] ] => rewrite to_nat_add
           | [ H : context [ to_nat (one_w _) ] |- _ ] => rewrite to_nat_one_w in H
           | [ |- context [ to_nat (one_w _) ] ] => rewrite to_nat_one_w
           | [ H : context [ to_nat (algebra.one _) ] |- _ ] => rewrite to_nat_one_a in H
           | [ |- context [ to_nat (algebra.one _) ] ] => rewrite to_nat_one_a
           end; lia.

  (** Cross-language compatibility for the forms used by linking *)

  Lemma E_a_fun_compat (P1 P2 PG : PostT_a) k rho1 rho2 B1 B2 e1 e2
        (HOOT : post_a_OOT P2) (Hcompat : post_a_fun P1 P2) :
    E_a PG P1 (k - 1) (e1, term.def_funs B1 B1 rho1 rho1) (e2, def_funs B2 B2 rho2 rho2) ->
    E_a PG P2 k (term.Efun B1 e1, rho1) (Efun B2 e2, rho2).
  Proof.
    intros Hexp r1 cin cout Hleq Hstep. inv Hstep.
    - exists OOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H.
      edestruct Hexp as (r2 & cin' & cout' & Hstep2 & Hpost & HR); [| eassumption |]. fuel_arith.
      do 3 eexists. split; [| split ].
      + econstructor 2; [ econstructor; eauto |]. intros _.
        destruct r2; simpl; eauto. eapply bstep_fuel_exposed_val; eauto.
      + eapply Hcompat; eauto.
      + eapply R_a_mono; eauto. fuel_arith.
  Qed.

  Definition fun_rel_a PG k (rho1 : aenv) (rho2 : env) f1 f2 :=
    forall v1, M.get f1 rho1 = Some v1 ->
               exists v2, M.get f2 rho2 = Some v2 /\ exposed_val v2 /\ V_a_fun PG (V_a PG) k v1 v2.

  Lemma E_a_letapp_compat (P1 P2 PG : PostT_a) k rho1 rho2 x f1 f2 t ys1 ys2 e1 e2
        (Hcompat : post_a_letapp P1 P2 PG) (HcompatOOT : post_a_letapp_OOT P2 PG)
        (HOOT : post_a_OOT P2) :
    fun_rel_a PG k rho1 rho2 f1 f2 ->
    Forall2 (var_rel_a PG k rho1 rho2) ys1 ys2 ->
    (forall m v1 v2, m < k -> V_a PG m v1 v2 ->
                     E_a PG P1 m (e1, M.set x v1 rho1) (e2, M.set x v2 rho2)) ->
    E_a PG P2 k (term.Eletapp x f1 t ys1 e1, rho1) (Eletapp x f2 t ys2 e2, rho2).
  Proof.
    intros Hfun Hall Hk r1 cin cout Hleq Hstep. inv Hstep.
    - exists OOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - assert (Hgetl : forall vs, get_list ys1 rho1 = Some vs ->
                                 exists vs2, get_list ys2 rho2 = Some vs2 /\ Forall2 (V_a PG k) vs vs2).
      { clear -Hall. induction Hall; intros vs Hget; simpl in *.
        - inv Hget. eauto.
        - destruct (M.get x rho1) eqn:Hx; try congruence.
          destruct (get_list l rho1) eqn:Hl; try congruence. inv Hget.
          edestruct H as (v2 & Hget2 & Hv); eauto.
          edestruct IHHall as (vs2 & Hgetl2 & Hvs); eauto.
          rewrite Hget2, Hgetl2. eauto. }
      inv H;
        (edestruct Hfun as (v2 & Hget2 & Hexpv2 & Hv); eauto;
         edestruct Hgetl as (vs2 & Hgetl2 & Hvs); eauto;
         destruct v2; try contradiction;
         edestruct (Hv vs vs2 (k - 1)) as (xs2 & eb2 & rho2' & Hf2 & Hset2 & Hbody); eauto;
         [ eapply Forall2_length; eauto | ];
         assert (Hte : exposedb t = true)
           by (rewrite exposed_val_Vfun in Hexpv2; destructAll; congruence);
         assert (Hexpvs : Forall exposed_val vs2)
           by (clear -Hvs; induction Hvs; constructor; eauto; eapply V_a_exposed; eauto)).
      + edestruct Hbody as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
          [ fuel_arith | | | eassumption | ]; [ | fuel_arith | ].
        * eapply Forall2_monotonic; [| eassumption ]. intros. eapply V_a_mono; eauto. lia.
        * destruct r2 as [| v2]; try contradiction. simpl in HR.
          edestruct (Hk (k - 1 - to_nat cin1)) as (r2 & cin'' & cout'' & Hstep3 & Hpost' & HR');
            [ fuel_arith | eassumption | | eassumption | ]; [ fuel_arith | ].
          do 3 eexists. split; [| split ].
          -- econstructor 2; [ econstructor; eauto; rewrite Hte; eauto |].
             intros _. destruct r2; simpl; eauto. eapply bstep_fuel_exposed_val; eauto.
          -- eapply Hcompat; eauto.
          -- eapply R_a_mono; eauto. fuel_arith.
      + edestruct Hbody as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
          [ fuel_arith | | | eassumption | ]; [ | fuel_arith | ].
        * eapply Forall2_monotonic; [| eassumption ]. intros. eapply V_a_mono; eauto. lia.
        * destruct r2; try contradiction.
          do 3 eexists. split; [| split ].
          -- econstructor 2; [ eapply BStept_letapp_oot; eauto; rewrite Hte; eauto |].
             intros; exact I.
          -- eapply HcompatOOT; eauto.
          -- exact I.
  Qed.

  Variable (lft : web).
  Hypothesis (Hlft : exposedb lft = true).

  Context (P : PostT_a) (PG : PostT_a) (Hpr : Post_properties_a P PG).

  (** Lemma 7.4: linking for annotation *)
  Theorem E_anno_preserves_linking x e1 e2 e1' e2' :
    identifiers.closed_exp e1 ->
    identifiers.occurs_free e1' \subset [set x] ->
    E_anno_top P PG e1 e2 ->
    E_anno_top P PG e1' e2' ->
    E_anno_top P PG (CertiRocq.LambdaANF.rel_comp.link lft x e1 e1') (link_w lft x e2 e2').
  Proof.
    intros Hc Hfv [Hfv1 Hlib] [Hfv2 Hcl]. inv Hpr. split.
    { assert (Hc2 : closed_exp e2).
      { split; [| sets ]. eapply Included_trans; [ eassumption | eapply Hc ]. }
      eapply link_closed in Hc2; [| eapply Included_trans; eassumption ].
      intros z Hz. eapply Hc2 in Hz. inv Hz. }
    intros k rho1 rho2 [Hwf2 HG] Hbind.
    unfold CertiRocq.LambdaANF.rel_comp.link, link_w, link.
    set (f1 := (identifiers.max_var e1 (identifiers.max_var e1' x) + 1)%positive).
    set (f2 := link_var x e2 e2').
    set (B1 := term.Fcons f1 lft [] e1 term.Fnil).
    set (B2 := Fcons f2 lft [] e2 Fnil).
    assert (Hwfc : wf_env (def_funs B2 B2 rho2 rho2)) by (eapply wf_env_def_funs; eauto).
    eapply E_a_fun_compat; eauto.
    eapply E_a_letapp_compat; eauto.
    - intros v1 Hget. simpl in Hget. rewrite M.gss in Hget. inv Hget.
      eexists. simpl. rewrite M.gss. split; [ reflexivity |].
      split; [ rewrite exposed_val_Vfun; do 3 eexists; simpl; rewrite peq_true; split; eauto |].
      unfold V_a_fun; cbn -[E_a']. intros vs1 vs2 j t xs1 eb1 rho1' Hlen Hfind Hset.
      rewrite peq_true in Hfind. inv Hfind. destruct vs1; simpl in Hset; try congruence.
      destruct vs2; simpl in Hlen; try congruence. inv Hset.
      do 3 eexists. split; [ simpl; rewrite peq_true; reflexivity | split; [ reflexivity |] ].
      intros Hj Hall r1 cin cout Hleq Hs.
      edestruct Hlib as (r2 & cin' & cout' & Hs2 & Hpost & HR);
        [ | | eassumption | eassumption | ].
      + split; [ eassumption |]. intros z Hz. eapply Hc in Hz. inv Hz.
      + intros z Hz. eapply Hc in Hz. inv Hz.
      + do 3 eexists; split; [ eassumption | split; [ eapply HPa_GPost0; eassumption | eassumption ] ].
    - intros m v1 v2 Hlt Hv. eapply Hcl.
      + split; [ eapply wf_env_set; eauto; eapply V_a_wf; eauto |].
        intros z Hz. eapply Hfv in Hz. inv Hz.
        intros v1' Hget. rewrite M.gss in Hget. inv Hget.
        eexists. rewrite M.gss. split; eauto.
      + intros z Hz. eapply Hfv in Hz. inv Hz. eexists. rewrite M.gss. reflexivity.
  Qed.

End Anno.
