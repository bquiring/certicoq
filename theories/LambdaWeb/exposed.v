(* The parameterized λweb logical relations (Fig. 5 of the paper), adapted
   to CertiRocq's λANF:

   - expression relations carry CertiRocq's local postcondition [P] and the
     value relation carries the global postcondition [PG], which relate the
     fuel and traces of the two executions (CertiRocq uses them for
     divergence preservation and cost bounds);
   - closures are mutually recursive bundles [Vfun ρ B f], and a function's
     web is found with [find_def];
   - there are base values ([Vprim], [Vint]).

   The relation is parameterized by a transformation-specific relation [VT]
   for internal (non-exposed) closures.  [VT] receives the value relation
   only at strictly smaller step indices, which makes the definition
   well-founded.  Internal constructor values are related structurally,
   like exposed ones; every case study of the paper does so.

   The main generic result is [V_exposed_indep] (Theorem 5.1): on exposed
   values the relation does not depend on [VT]. *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations Classes.Morphisms.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics algebra set_util.
From CertiRocq.LambdaANF Require term term_util.
From CertiRocq.LambdaWeb Require Import syntax semantics.

Import ListNotations.

Open Scope alg_scope.

Section Rel.

  Variable (cenv : term.ctor_env).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Definition PostT : Type := relation (exp * env * fuel * trace).
  Definition PostGT : Type := relation (exp * env * fuel * trace).

  (** * Result and expression relations, parameterized by a value relation *)

  Definition R' (V : nat -> val -> val -> Prop) (k : nat) (r1 r2 : res) : Prop :=
    match r1, r2 with
    | OOT, OOT => True
    | Res v1, Res v2 => V k v1 v2
    | _, _ => False
    end.

  Definition E' (V : nat -> val -> val -> Prop) (P : PostT) (ex : bool) (k : nat)
             (p1 p2 : exp * env) : Prop :=
    let '(e1, rho1) := p1 in
    let '(e2, rho2) := p2 in
    forall r1 cin cout,
      to_nat cin <= k ->
      bstep_fuel cenv ex rho1 e1 cin r1 cout ->
      exists r2 cin' cout',
        bstep_fuel cenv ex rho2 e2 cin' r2 cout' /\
        P (e1, rho1, cin, cout) (e2, rho2, cin', cout') /\
        R' V (k - to_nat cin) r1 r2.

  (** Relation for closures that keep their calling convention.  This is
      CertiRocq's [preord_val] function case, where the function tag is now
      the web of the function.  The function body is evaluated with the
      exposure flag of its web, and arguments of exposed functions are
      exposed. *)
  Definition V_fun (PG : PostGT) (V' : nat -> val -> val -> Prop) (k : nat) (v1 v2 : val) : Prop :=
    match v1, v2 with
    | Vfun rho1 B1 f1, Vfun rho2 B2 f2 =>
        forall vs1 vs2 j w xs1 e1 rho1',
          length vs1 = length vs2 ->
          find_def f1 B1 = Some (w, xs1, e1) ->
          Some rho1' = set_lists xs1 vs1 (def_funs B1 B1 rho1 rho1) ->
          exists xs2 e2 rho2',
            find_def f2 B2 = Some (w, xs2, e2) /\
            Some rho2' = set_lists xs2 vs2 (def_funs B2 B2 rho2 rho2) /\
            (j < k ->
             (exposedb w = true -> Forall exposed_val vs1) ->
             Forall2 (V' j) vs1 vs2 ->
             E' V' PG (exposedb w) j (e1, rho1') (e2, rho2'))
    | _, _ => False
    end.

  (** The type of transformation-specific relations for internal closures. *)
  Definition VTransT : Type := PostGT -> (nat -> val -> val -> Prop) -> nat -> val -> val -> Prop.

  (** Web of a closure value *)
  Definition val_web (v : val) : option web :=
    match v with
    | Vfun _ B f => fun_web B f
    | _ => None
    end.

  (** * The value relation *)

  Fixpoint V (VT : VTransT) (PG : PostGT) (k : nat) (v1 v2 : val) {struct k} : Prop :=
    let V' : nat -> val -> val -> Prop :=
      match k with
      | 0 => fun _ _ _ => False
      | S k0 => fun j => V VT PG (k0 - (k0 - j))
      end in
    let fix Vi (v1 v2 : val) {struct v1} : Prop :=
      let fix Forall2_aux vs1 vs2 :=
        match vs1, vs2 with
        | [], [] => True
        | v1 :: vs1, v2 :: vs2 => Vi v1 v2 /\ Forall2_aux vs1 vs2
        | _, _ => False
        end in
      wf_val v1 /\ wf_val v2 /\ (exposed_val v1 <-> exposed_val v2) /\
      match v1, v2 with
      | Vconstr w1 t1 vs1, Vconstr w2 t2 vs2 => w1 = w2 /\ t1 = t2 /\ Forall2_aux vs1 vs2
      | Vfun _ B1 f1, _ =>
          match fun_web B1 f1 with
          | Some w => if exposedb w then V_fun PG V' k v1 v2 else VT PG V' k v1 v2
          | None => VT PG V' k v1 v2
          end
      | Vprim p1, Vprim p2 => p1 = p2
      | Vint z1, Vint z2 => z1 = z2
      | _, _ => False
      end
    in Vi v1 v2.

  (** Unfolded form of the value relation *)
  Definition V_ (VT : VTransT) (PG : PostGT) (k : nat) (v1 v2 : val) : Prop :=
    wf_val v1 /\ wf_val v2 /\ (exposed_val v1 <-> exposed_val v2) /\
    match v1, v2 with
    | Vconstr w1 t1 vs1, Vconstr w2 t2 vs2 => w1 = w2 /\ t1 = t2 /\ Forall2 (V VT PG k) vs1 vs2
    | Vfun _ B1 f1, _ =>
        match fun_web B1 f1 with
        | Some w => if exposedb w then V_fun PG (V VT PG) k v1 v2 else VT PG (V VT PG) k v1 v2
        | None => VT PG (V VT PG) k v1 v2
        end
    | Vprim p1, Vprim p2 => p1 = p2
    | Vint z1, Vint z2 => z1 = z2
    | _, _ => False
    end.

  (** Requirements on transformation-specific relations: they may only
      depend on the value relation below the current index, and they must be
      monotone. *)
  Class VTransProps (VT : VTransT) : Prop :=
    { VT_ext :
        forall PG V1 V2 k v1 v2,
          (forall j, j < k -> forall v1 v2, V1 j v1 v2 <-> V2 j v1 v2) ->
          VT PG V1 k v1 v2 -> VT PG V2 k v1 v2;
      VT_mono :
        forall PG V k j v1 v2,
          (forall m l v1 v2, m < k -> l <= m -> V m v1 v2 -> V l v1 v2) ->
          VT PG V k v1 v2 -> j <= k -> VT PG V j v1 v2 }.

  (** ** Extensionality and monotonicity of the generic pieces *)

  Lemma R'_ext V1 V2 k r1 r2 :
    (forall v1 v2, V1 k v1 v2 <-> V2 k v1 v2) ->
    R' V1 k r1 r2 <-> R' V2 k r1 r2.
  Proof. intros H; destruct r1, r2; simpl; try tauto; apply H. Qed.

  Lemma E'_ext V1 V2 P ex k p1 p2 :
    (forall j, j <= k -> forall v1 v2, V1 j v1 v2 <-> V2 j v1 v2) ->
    E' V1 P ex k p1 p2 -> E' V2 P ex k p1 p2.
  Proof.
    destruct p1 as [e1 rho1], p2 as [e2 rho2]. simpl.
    intros Hext HE r1 cin cout Hleq Hstep.
    edestruct HE as (r2 & cin' & cout' & Hstep' & HP & HR); eauto.
    do 3 eexists; split; [ eassumption | split; [ eassumption |] ].
    destruct r1, r2; simpl in *; eauto. eapply Hext; eauto. lia.
  Qed.

  Lemma V_fun_ext PG V1 V2 k v1 v2 :
    (forall j, j < k -> forall v1 v2, V1 j v1 v2 <-> V2 j v1 v2) ->
    V_fun PG V1 k v1 v2 -> V_fun PG V2 k v1 v2.
  Proof.
    destruct v1, v2; cbn -[E']; try easy.
    intros Hext Hfn vs1 vs2 j w xs1 e1 rho1' Hlen Hfind Hset.
    edestruct (Hfn vs1 vs2 j w xs1 e1 rho1' Hlen Hfind Hset) as (xs2 & e2 & rho2' & Hfind2 & Hset2 & Hbody).
    do 3 eexists. split; [ eassumption | split; [ eassumption |] ].
    intros Hlt Hexp Hall. eapply E'_ext; [| eapply Hbody; eauto ].
    - intros. eapply Hext. lia.
    - eapply Forall2_monotonic; [| eassumption ]. intros. eapply Hext; eauto.
  Qed.

  Lemma R'_mono (V : nat -> val -> val -> Prop) k j r1 r2 :
    (forall v1 v2, V k v1 v2 -> V j v1 v2) ->
    R' V k r1 r2 -> R' V j r1 r2.
  Proof. destruct r1, r2; simpl; eauto. Qed.

  Lemma E'_mono (V : nat -> val -> val -> Prop) P ex k j p1 p2 :
    (forall m l v1 v2, m <= k -> l <= m -> V m v1 v2 -> V l v1 v2) ->
    E' V P ex k p1 p2 -> j <= k -> E' V P ex j p1 p2.
  Proof.
    destruct p1 as [e1 rho1], p2 as [e2 rho2]. simpl.
    intros Hmono HE Hleq r1 cin cout Hleq' Hstep.
    edestruct HE as (r2 & cin' & cout' & Hstep' & HP & HR); [| eassumption |]; [ lia |].
    do 3 eexists; split; [ eassumption | split; [ eassumption |] ].
    eapply R'_mono; [| eassumption ]. intros. eapply Hmono; [| | eassumption ]; lia.
  Qed.

  Lemma V_fun_mono PG (V : nat -> val -> val -> Prop) k j v1 v2 :
    V_fun PG V k v1 v2 -> j <= k -> V_fun PG V j v1 v2.
  Proof.
    destruct v1, v2; cbn -[E']; try easy.
    intros Hfn Hleq vs1 vs2 i w xs1 e1 rho1' Hlen Hfind Hset.
    edestruct (Hfn vs1 vs2 i w xs1 e1 rho1' Hlen Hfind Hset) as (xs2 & e2 & rho2' & Hfind2 & Hset2 & Hbody).
    do 3 eexists. split; [ eassumption | split; [ eassumption |] ].
    intros Hlt. eapply Hbody. lia.
  Qed.

  Lemma V_fun_Vfun_inv PG V' k v1 v2 :
    V_fun PG V' k v1 v2 ->
    exists rho1 B1 f1 rho2 B2 f2, v1 = Vfun rho1 B1 f1 /\ v2 = Vfun rho2 B2 f2.
  Proof. destruct v1, v2; simpl; try easy. intros. do 6 eexists; eauto. Qed.

  Lemma Forall2_aux_eq {A B} (Vi : A -> B -> Prop) (vs1 : list A) (vs2 : list B) :
    (fix Forall2_aux (vs1 : list A) (vs2 : list B) :=
       match vs1, vs2 with
       | [], [] => True
       | v1 :: vs1, v2 :: vs2 => Vi v1 v2 /\ Forall2_aux vs1 vs2
       | _, _ => False
       end) vs1 vs2 <-> Forall2 Vi vs1 vs2.
  Proof.
    revert vs2; induction vs1; intros vs2; destruct vs2; split; intros H; try easy;
      try (now inv H).
    - destruct H. constructor; eauto. eapply IHvs1; eauto.
    - inv H. split; eauto. eapply IHvs1; eauto.
  Qed.

  Section WithVT.

    Context (VT : VTransT) {HVT : VTransProps VT}.


    Lemma clamp_ext PG k0 :
      forall j, j < S k0 -> forall v1 v2,
        V VT PG (k0 - (k0 - j)) v1 v2 <-> V VT PG j v1 v2.
    Proof. intros j Hj v1 v2. replace (k0 - (k0 - j)) with j by lia. reflexivity. Qed.

    Lemma V_eq PG k v1 v2 : V VT PG k v1 v2 <-> V_ VT PG k v1 v2.
    Proof.
      revert v2. induction v1 using val_ind_Forall; intros v2;
        unfold V_; destruct k as [| k0]; cbn -[V_fun]; try reflexivity.
      - destruct v2; try reflexivity.
        rewrite Forall2_aux_eq. reflexivity.
      - destruct v2; try reflexivity.
        rewrite Forall2_aux_eq. reflexivity.
      - destruct (fun_web B f) as [w |]; [ destruct (exposedb w) |].
        + split; intros (H1 & H2 & H3 & H4); repeat (split; [ eassumption |]);
            eapply V_fun_ext; try eassumption; intros; lia.
        + split; intros (H1 & H2 & H3 & H4); repeat (split; [ eassumption |]);
            eapply VT_ext; try eassumption; intros; lia.
        + split; intros (H1 & H2 & H3 & H4); repeat (split; [ eassumption |]);
            eapply VT_ext; try eassumption; intros; lia.
      - destruct (fun_web B f) as [w |]; [ destruct (exposedb w) |].
        + split; intros (H1 & H2 & H3 & H4); repeat (split; [ eassumption |]);
            eapply V_fun_ext; try eassumption; intros; rewrite clamp_ext by lia; reflexivity.
        + split; intros (H1 & H2 & H3 & H4); repeat (split; [ eassumption |]);
            eapply VT_ext; try eassumption; intros; rewrite clamp_ext by lia; reflexivity.
        + split; intros (H1 & H2 & H3 & H4); repeat (split; [ eassumption |]);
            eapply VT_ext; try eassumption; intros; rewrite clamp_ext by lia; reflexivity.
    Qed.

    Global Opaque V.

    Definition R PG := R' (V VT PG).
    Definition E PG P ex k p1 p2 := E' (V VT PG) P ex k p1 p2.

    (** ** Basic properties *)

    Lemma V_wf_l PG k v1 v2 : V VT PG k v1 v2 -> wf_val v1.
    Proof. rewrite V_eq. intros H; apply H. Qed.

    Lemma V_wf_r PG k v1 v2 : V VT PG k v1 v2 -> wf_val v2.
    Proof. rewrite V_eq. intros H; apply H. Qed.

    Lemma V_exposed PG k v1 v2 : V VT PG k v1 v2 -> exposed_val v1 <-> exposed_val v2.
    Proof. rewrite V_eq. intros H; apply H. Qed.

    Lemma Forall2_V_wf_l PG k vs1 vs2 : Forall2 (V VT PG k) vs1 vs2 -> Forall wf_val vs1.
    Proof. intros H; induction H; constructor; eauto using V_wf_l. Qed.

    Lemma Forall2_V_wf_r PG k vs1 vs2 : Forall2 (V VT PG k) vs1 vs2 -> Forall wf_val vs2.
    Proof. intros H; induction H; constructor; eauto using V_wf_r. Qed.

    Lemma Forall2_V_exposed PG k vs1 vs2 :
      Forall2 (V VT PG k) vs1 vs2 -> Forall exposed_val vs1 <-> Forall exposed_val vs2.
    Proof.
      intros H; induction H; split; intros Hall; inv Hall; constructor; try (eapply IHForall2; eauto).
      - eapply (V_exposed _ _ _ _ H); eauto.
      - eapply (V_exposed _ _ _ _ H); eauto.
    Qed.

    Lemma R_exposed PG k r1 r2 : R PG k r1 r2 -> exposed_res r1 <-> exposed_res r2.
    Proof. destruct r1, r2; simpl; try easy. eapply V_exposed. Qed.

    Lemma R_wf_l PG k r1 r2 : R PG k r1 r2 -> wf_res r1.
    Proof. destruct r1, r2; simpl; try easy. eapply V_wf_l. Qed.

    Lemma R_wf_r PG k r1 r2 : R PG k r1 r2 -> wf_res r2.
    Proof. destruct r1, r2; simpl; try easy. eapply V_wf_r. Qed.

    (** ** Monotonicity *)

    Lemma V_mono PG k : forall j v1 v2, V VT PG k v1 v2 -> j <= k -> V VT PG j v1 v2.
    Proof.
      induction k as [k IHk] using lt_wf_rec.
      intros j v1. revert j.
      induction v1 using val_ind_Forall; intros j v2 Hv Hleq;
        rewrite V_eq in *; unfold V_ in *; destructAll; repeat (split; [ eassumption |]).
      - destruct v2; try contradiction. destructAll. split; eauto. split; eauto.
        clear H0 H1 H2. revert l H5. induction H; intros l2 Hall; inv Hall; constructor; eauto.
      - assert (Hmono : forall m l v1 v2, m < k -> l <= m -> V VT PG m v1 v2 -> V VT PG l v1 v2).
        { intros. eapply IHk; eauto. }
        destruct (fun_web B f) as [w |]; [ destruct (exposedb w) |].
        + eapply V_fun_mono; eauto.
        + eapply VT_mono; eauto.
        + eapply VT_mono; eauto.
      - destruct v2; try contradiction. eauto.
      - destruct v2; try contradiction. eauto.
    Qed.

    Lemma V_mono_Forall2 PG k j vs1 vs2 :
      Forall2 (V VT PG k) vs1 vs2 -> j <= k -> Forall2 (V VT PG j) vs1 vs2.
    Proof.
      intros H Hleq. eapply Forall2_monotonic; [| eassumption ]. intros. eapply V_mono; eauto.
    Qed.

    Lemma R_mono PG k j r1 r2 : R PG k r1 r2 -> j <= k -> R PG j r1 r2.
    Proof. intros H Hleq. eapply R'_mono; [| eassumption ]. intros. eapply V_mono; eauto. Qed.

    Lemma E_mono PG P ex k j p1 p2 : E PG P ex k p1 p2 -> j <= k -> E PG P ex j p1 p2.
    Proof. intros H Hleq. eapply E'_mono; eauto. intros. eapply V_mono; eauto. Qed.

    Lemma E_post_mono PG (P1 P2 : PostT) ex k p1 p2 :
      inclusion _ P1 P2 -> E PG P1 ex k p1 p2 -> E PG P2 ex k p1 p2.
    Proof.
      destruct p1 as [e1 rho1], p2 as [e2 rho2]. unfold E, E'.
      intros Hinc HE r1 cin cout Hleq Hstep.
      edestruct HE as (r2 & cin' & cout' & Hstep' & HP & HR); eauto.
      do 3 eexists; split; [ eassumption | split; [ eapply Hinc; eassumption | eassumption ] ].
    Qed.

    (** ** Shapes of related values *)

    Lemma V_Vconstr_l PG k w t vs1 v2 :
      V VT PG k (Vconstr w t vs1) v2 ->
      exists vs2, v2 = Vconstr w t vs2 /\ Forall2 (V VT PG k) vs1 vs2.
    Proof.
      rewrite V_eq. unfold V_. intros. destructAll. destruct v2; try contradiction. destructAll. eauto.
    Qed.

    Lemma V_Vconstr PG k w t vs1 vs2 :
      (exposedb w = true -> Forall exposed_val vs1) ->
      Forall2 (V VT PG k) vs1 vs2 ->
      V VT PG k (Vconstr w t vs1) (Vconstr w t vs2).
    Proof.
      intros Hexp Hall. rewrite V_eq. unfold V_.
      assert (Hexp2 : exposedb w = true -> Forall exposed_val vs2).
      { intros Hw. eapply (proj1 (Forall2_V_exposed _ _ _ _ Hall)); eauto. }
      split; [| split; [| split ] ].
      - constructor; eauto. eapply Forall2_V_wf_l; eauto.
      - constructor; eauto. eapply Forall2_V_wf_r; eauto.
      - rewrite !exposed_val_Vconstr. pose proof (Forall2_V_exposed _ _ _ _ Hall) as Hiff.
        split; intros [Hw Hvs]; split; eauto; eapply Hiff; eauto.
      - eauto.
    Qed.

    Lemma V_exposed_fun PG k rho1 B1 f1 w v2 :
      V VT PG k (Vfun rho1 B1 f1) v2 ->
      fun_web B1 f1 = Some w ->
      exposedb w = true ->
      V_fun PG (V VT PG) k (Vfun rho1 B1 f1) v2.
    Proof.
      rewrite V_eq. unfold V_. intros. destructAll. rewrite H0, H1 in *. eassumption.
    Qed.

    Lemma V_internal_fun PG k rho1 B1 f1 v2 :
      V VT PG k (Vfun rho1 B1 f1) v2 ->
      ~ exposed_val (Vfun rho1 B1 f1) ->
      VT PG (V VT PG) k (Vfun rho1 B1 f1) v2.
    Proof.
      rewrite V_eq. unfold V_. intros. destructAll.
      rewrite exposed_val_Vfun in H0. unfold fun_web in *.
      destruct (find_def f1 B1) as [[[w xs] e] |]; eauto.
      destruct (exposedb w) eqn:Hw; eauto. exfalso; eapply H0; do 3 eexists; split; eauto.
    Qed.

    (** Introduction rule for closures with an exposed web *)
    Lemma V_Vfun_exposed PG k rho1 B1 f1 rho2 B2 f2 w xs1 e1 xs2 e2 :
      wf_env rho1 -> wf_env rho2 ->
      find_def f1 B1 = Some (w, xs1, e1) ->
      find_def f2 B2 = Some (w, xs2, e2) ->
      exposedb w = true ->
      V_fun PG (V VT PG) k (Vfun rho1 B1 f1) (Vfun rho2 B2 f2) ->
      V VT PG k (Vfun rho1 B1 f1) (Vfun rho2 B2 f2).
    Proof.
      intros Hwf1 Hwf2 Hf1 Hf2 Hw Hfun. rewrite V_eq. unfold V_.
      split; [ constructor; eauto | split; [ constructor; eauto | split ] ].
      - rewrite !exposed_val_Vfun. split; intros; eauto 10.
      - unfold fun_web. rewrite Hf1, Hw. eassumption.
    Qed.

    (** Introduction rule for internal closures *)
    Lemma V_Vfun_internal PG k rho1 B1 f1 v2 :
      wf_env rho1 -> wf_val v2 ->
      ~ exposed_val (Vfun rho1 B1 f1) ->
      ~ exposed_val v2 ->
      VT PG (V VT PG) k (Vfun rho1 B1 f1) v2 ->
      V VT PG k (Vfun rho1 B1 f1) v2.
    Proof.
      intros Hwf1 Hwf2 Hn1 Hn2 Hvt. rewrite V_eq. unfold V_.
      split; [ constructor; eauto | split; [ eauto | split ] ].
      - tauto.
      - rewrite exposed_val_Vfun in Hn1. unfold fun_web.
        destruct (find_def f1 B1) as [[[w xs] e] |]; eauto.
        destruct (exposedb w) eqn:Hw; eauto. exfalso; eapply Hn1; do 3 eexists; split; eauto.
    Qed.

    (** ** Environment relations *)

    Definition var_rel PG k rho1 rho2 x y : Prop :=
      forall v1, M.get x rho1 = Some v1 ->
                 exists v2, M.get y rho2 = Some v2 /\ V VT PG k v1 v2.

    Definition G PG k (S : Ensemble var) (rho1 rho2 : env) : Prop :=
      wf_env rho1 /\ wf_env rho2 /\ forall x, S x -> var_rel PG k rho1 rho2 x x.

    Lemma var_rel_mono PG k j rho1 rho2 x y :
      var_rel PG k rho1 rho2 x y -> j <= k -> var_rel PG j rho1 rho2 x y.
    Proof.
      intros H Hleq v1 Hget. edestruct H as (v2 & Hget2 & Hv); eauto.
      eexists; split; eauto. eapply V_mono; eauto.
    Qed.

    Lemma G_mono PG k j S rho1 rho2 : G PG k S rho1 rho2 -> j <= k -> G PG j S rho1 rho2.
    Proof.
      intros (H1 & H2 & H3) Hleq. split; [| split ]; eauto.
      intros. eapply var_rel_mono; eauto.
    Qed.

    Lemma G_antimon PG k S1 S2 rho1 rho2 : G PG k S2 rho1 rho2 -> S1 \subset S2 -> G PG k S1 rho1 rho2.
    Proof. intros (H1 & H2 & H3) Hsub. split; [| split ]; eauto. intros x Hx. eapply H3. eapply Hsub. eassumption. Qed.

    Lemma G_wf_l PG k S rho1 rho2 : G PG k S rho1 rho2 -> wf_env rho1.
    Proof. intros H; apply H. Qed.

    Lemma G_wf_r PG k S rho1 rho2 : G PG k S rho1 rho2 -> wf_env rho2.
    Proof. intros H; apply H. Qed.

    Lemma G_var_rel PG k S rho1 rho2 x : G PG k S rho1 rho2 -> S x -> var_rel PG k rho1 rho2 x x.
    Proof. intros (_ & _ & H) Hin. eauto. Qed.

    Lemma G_empty PG k rho1 rho2 : wf_env rho1 -> wf_env rho2 -> G PG k (Empty_set _) rho1 rho2.
    Proof. intros. split; [| split ]; eauto. intros x Hin. inv Hin. Qed.

    Lemma var_rel_get_list PG k rho1 rho2 xs ys vs1 :
      Forall2 (var_rel PG k rho1 rho2) xs ys ->
      get_list xs rho1 = Some vs1 ->
      exists vs2, get_list ys rho2 = Some vs2 /\ Forall2 (V VT PG k) vs1 vs2.
    Proof.
      revert ys vs1. induction xs as [| x xs IHxs]; intros ys vs1 Hall Hget.
      - destruct ys; inv Hall. inv Hget. eexists. split; simpl; eauto.
      - simpl in Hget.
        destruct (M.get x rho1) eqn:Heq1; try discriminate.
        destruct (get_list xs rho1) eqn:Heq2; try discriminate. inv Hget.
        destruct ys as [| y ys]; inv Hall.
        destruct (IHxs ys l H4 eq_refl) as [vs2 [Hget HAll]].
        destruct (H2 _ Heq1) as [v2 [Heq Hpre]].
        eexists. split; simpl; eauto. rewrite Hget, Heq. eauto.
    Qed.

    Lemma G_Forall2_var_rel PG k S rho1 rho2 xs :
      G PG k S rho1 rho2 -> FromList xs \subset S -> Forall2 (var_rel PG k rho1 rho2) xs xs.
    Proof.
      intros HG Hsub. induction xs; constructor.
      - eapply G_var_rel; eauto. eapply Hsub. now left.
      - eapply IHxs. intros z Hz. eapply Hsub. now right.
    Qed.

    Lemma G_get_list PG k S rho1 rho2 xs vs1 :
      G PG k S rho1 rho2 -> FromList xs \subset S -> get_list xs rho1 = Some vs1 ->
      exists vs2, get_list xs rho2 = Some vs2 /\ Forall2 (V VT PG k) vs1 vs2.
    Proof. intros. eapply var_rel_get_list; eauto. eapply G_Forall2_var_rel; eauto. Qed.

    Lemma G_set PG k S rho1 rho2 x v1 v2 :
      G PG k (Setminus _ S [set x]) rho1 rho2 -> V VT PG k v1 v2 ->
      G PG k S (M.set x v1 rho1) (M.set x v2 rho2).
    Proof.
      intros (Hwf1 & Hwf2 & HG) Hv.
      split; [ eapply wf_env_set; [ eassumption | eapply V_wf_l; eassumption ] |].
      split; [ eapply wf_env_set; [ eassumption | eapply V_wf_r; eassumption ] |].
      intros y Hy v1' Hget. rewrite M.gsspec in *. destruct (peq y x); subst.
      - inv Hget. eauto.
      - eapply HG; eauto. constructor; eauto. intros Hc; inv Hc; eauto.
    Qed.

    Lemma G_set_lists PG k S rho1 rho2 rho1' rho2' xs vs1 vs2 :
      G PG k (Setminus _ S (FromList xs)) rho1 rho2 ->
      Forall2 (V VT PG k) vs1 vs2 ->
      set_lists xs vs1 rho1 = Some rho1' ->
      set_lists xs vs2 rho2 = Some rho2' ->
      G PG k S rho1' rho2'.
    Proof.
      revert S vs1 vs2 rho1' rho2'.
      induction xs as [| x xs IHxs]; intros S vs1 vs2 rho1' rho2' HG Hall Hs1 Hs2;
        destruct vs1, vs2; simpl in *; try congruence; inv Hall.
      - inv Hs1; inv Hs2. eapply G_antimon; eauto. rewrite FromList_nil. sets.
      - destruct (set_lists xs vs1 rho1) eqn:Hs1'; try congruence.
        destruct (set_lists xs vs2 rho2) eqn:Hs2'; try congruence. inv Hs1; inv Hs2.
        eapply G_set; eauto. eapply IHxs; eauto.
        eapply G_antimon; eauto. rewrite FromList_cons. intros z Hz. inv Hz. inv H.
        constructor; eauto. intros Hc. inv Hc; eauto.
    Qed.

    Lemma G_set_l_not_in PG k S rho1 rho2 x v :
      G PG k S rho1 rho2 -> wf_val v -> ~ S x -> G PG k S (M.set x v rho1) rho2.
    Proof.
      intros (Hwf1 & Hwf2 & HG) Hv Hnin. split; [| split ]; eauto using wf_env_set.
      intros y Hy v1 Hget. rewrite M.gso in Hget; [ eapply HG; eauto |].
      intros Hc; subst; eauto.
    Qed.

    Lemma G_set_r_not_in PG k S rho1 rho2 x v :
      G PG k S rho1 rho2 -> wf_val v -> ~ S x -> G PG k S rho1 (M.set x v rho2).
    Proof.
      intros (Hwf1 & Hwf2 & HG) Hv Hnin. split; [| split ]; eauto using wf_env_set.
      intros y Hy v1 Hget. edestruct HG as (v2 & Hget2 & Hv'); eauto.
      eexists; split; eauto. rewrite M.gso; eauto. intros Hc; subst; eauto.
    Qed.

    (** The environments extended with related mutually recursive bundles
        are related. *)
    Lemma G_def_funs PG k S rho1 rho2 B1 B2 rhoc1 rhoc2 :
      G PG k (Setminus _ S (name_in_fundefs B1)) rho1 rho2 ->
      wf_env rhoc1 -> wf_env rhoc2 ->
      (forall f, name_in_fundefs B1 f <-> name_in_fundefs B2 f) ->
      (forall f, name_in_fundefs B1 f -> V VT PG k (Vfun rhoc1 B1 f) (Vfun rhoc2 B2 f)) ->
      G PG k S (def_funs B1 B1 rhoc1 rho1) (def_funs B2 B2 rhoc2 rho2).
    Proof.
      intros (Hwf1 & Hwf2 & HG) Hc1 Hc2 Hnames Hfuns.
      split; [| split ]; try (eapply wf_env_def_funs; eauto).
      intros x Hx v1 Hget.
      destruct (name_in_fundefs_dec B1 x) as [Hin | Hnin].
      - rewrite def_funs_eq in Hget; eauto. inv Hget.
        eexists. rewrite def_funs_eq; [| now eapply Hnames ]. eauto.
      - rewrite def_funs_neq in Hget; eauto.
        edestruct HG as (v2 & Hget2 & Hv); eauto. constructor; eauto.
        eexists; split; eauto.
        rewrite def_funs_neq; eauto. intros Hc. eapply Hnin, Hnames; eauto.
    Qed.

  End WithVT.

End Rel.

#[global] Hint Extern 1 (VTransProps _) => typeclasses eauto : core.
