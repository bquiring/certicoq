(* An implementation of DPE with dead-binding elimination, and the proof that
   it inhabits the relation of dpe.v.

   - The analysis [masks] computes, for every internal web, the parameters
     that are used by some function of the web (a parameter is live if it
     occurs free in the body).  Webs whose functions do not agree on their
     arity are left out of the map, so they are not transformed.
   - The transformation [dpe] drops the dead parameters of the functions of
     the webs in the map and the corresponding arguments of their calls, and
     drops the [Econstr], [Eproj] and [Efun] bindings whose variables are
     dead in the transformed continuation.
   - The budget of removed bindings is the size of the program. *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics set_util.
From CertiRocq.LambdaANF Require identifiers.
From CertiRocq.LambdaWeb Require Import syntax semantics exposed post select indep bound comp dpe.

Import ListNotations.

(** * Preliminaries *)

(** Mutual induction on expressions and bundles *)
Lemma exp_fundefs_ind (P : exp -> Prop) (Q : fundefs -> Prop) :
  (forall x w t ys e, P e -> P (Econstr x w t ys e)) ->
  (forall x w, P (Ecase x w nil)) ->
  (forall x w cl c e, P e -> P (Ecase x w cl) -> P (Ecase x w ((c, e) :: cl))) ->
  (forall x w t n y e, P e -> P (Eproj x w t n y e)) ->
  (forall x f w ys e, P e -> P (Eletapp x f w ys e)) ->
  (forall B e, Q B -> P e -> P (Efun B e)) ->
  (forall f w ys, P (Eapp f w ys)) ->
  (forall x p e, P e -> P (Eprim_val x p e)) ->
  (forall x p ys e, P e -> P (Eprim x p ys e)) ->
  (forall x, P (Ehalt x)) ->
  (forall f w xs e B, P e -> Q B -> Q (Fcons f w xs e B)) ->
  Q Fnil ->
  (forall e, P e) /\ (forall B, Q B).
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
  refine (conj
            (fix Fe (e : exp) : P e :=
               match e with
               | Econstr x w t ys k => H1 x w t ys k (Fe k)
               | Ecase x w cl =>
                   (fix Fcl (cl : list (ctor_tag * exp)) : P (Ecase x w cl) :=
                      match cl with
                      | [] => H2 x w
                      | (c, k) :: cl' => H3 x w cl' c k (Fe k) (Fcl cl')
                      end) cl
               | Eproj x w t n y k => H4 x w t n y k (Fe k)
               | Eletapp x f w ys k => H5 x f w ys k (Fe k)
               | Efun B k => H6 B k (Fb B) (Fe k)
               | Eapp f w ys => H7 f w ys
               | Eprim_val x p k => H8 x p k (Fe k)
               | Eprim x p ys k => H9 x p ys k (Fe k)
               | Ehalt x => H10 x
               end
             with Fb (B : fundefs) : Q B :=
               match B with
               | Fcons f w xs k B' => H11 f w xs k B' (Fe k) (Fb B')
               | Fnil => H12
               end
             for Fe)
            (fix Fe (e : exp) : P e :=
               match e with
               | Econstr x w t ys k => H1 x w t ys k (Fe k)
               | Ecase x w cl =>
                   (fix Fcl (cl : list (ctor_tag * exp)) : P (Ecase x w cl) :=
                      match cl with
                      | [] => H2 x w
                      | (c, k) :: cl' => H3 x w cl' c k (Fe k) (Fcl cl')
                      end) cl
               | Eproj x w t n y k => H4 x w t n y k (Fe k)
               | Eletapp x f w ys k => H5 x f w ys k (Fe k)
               | Efun B k => H6 B k (Fb B) (Fe k)
               | Eapp f w ys => H7 f w ys
               | Eprim_val x p k => H8 x p k (Fe k)
               | Eprim x p ys k => H9 x p ys k (Fe k)
               | Ehalt x => H10 x
               end
             with Fb (B : fundefs) : Q B :=
               match B with
               | Fcons f w xs k B' => H11 f w xs k B' (Fe k) (Fb B')
               | Fnil => H12
               end
             for Fb)).
Qed.

(** Free variables, computed by CertiRocq's [exp_fv] *)
Definition is_free (e : exp) (z : var) : bool := PS.mem z (identifiers.exp_fv (erase e)).

Lemma is_free_spec e z : is_free e z = true <-> occurs_free e z.
Proof.
  unfold is_free, occurs_free. rewrite PS.mem_spec. split; intros H.
  - eapply FromSet_complete; [ eapply identifiers.exp_fv_correct | eassumption ].
  - eapply FromSet_sound; [ eapply identifiers.exp_fv_correct | eassumption ].
Qed.

Lemma is_free_false e z : is_free e z = false -> ~ occurs_free e z.
Proof. intros H Hc. eapply is_free_spec in Hc. congruence. Qed.

Fixpoint bnames (B : fundefs) : list var :=
  match B with
  | Fcons f _ _ _ B => f :: bnames B
  | Fnil => []
  end.

Lemma name_in_bnames B x : name_in_fundefs B x -> List.In x (bnames B).
Proof.
  induction B; simpl; intros H; [| inv H ].
  destruct H as [x H | x H]; [ inv H; now left | right; eauto ].
Qed.

(** Size of an expression; it bounds the number of bindings on any path *)
Fixpoint esize (e : exp) : nat :=
  match e with
  | Econstr _ _ _ _ k | Eproj _ _ _ _ _ k | Eletapp _ _ _ _ k
  | Eprim_val _ _ k | Eprim _ _ _ k => S (esize k)
  | Ecase _ _ cl =>
      S ((fix go (cl : list (ctor_tag * exp)) :=
            match cl with
            | [] => 0
            | (_, e) :: cl => esize e + go cl
            end) cl)
  | Efun B k => S (fsize B + esize k)
  | Eapp _ _ _ | Ehalt _ => 1
  end
with fsize (B : fundefs) : nat :=
  match B with
  | Fcons _ _ _ e B => S (esize e + fsize B)
  | Fnil => 0
  end.

(** * The analysis *)

(** [None]: the functions of the web disagree on their arity *)
Definition entry : Type := option (list bool).

Fixpoint join_bool (bs1 bs2 : list bool) : list bool :=
  match bs1, bs2 with
  | b1 :: bs1, b2 :: bs2 => orb b1 b2 :: join_bool bs1 bs2
  | _, _ => []
  end.

Definition add_mask (w : web) (m : list bool) (tbl : M.t entry) : M.t entry :=
  match tbl ! w with
  | None => M.set w (Some m) tbl
  | Some None => tbl
  | Some (Some m') =>
      if Nat.eqb (length m') (length m) then M.set w (Some (join_bool m' m)) tbl
      else M.set w None tbl
  end.

Fixpoint collect (e : exp) (tbl : M.t entry) : M.t entry :=
  match e with
  | Econstr _ _ _ _ k | Eproj _ _ _ _ _ k | Eletapp _ _ _ _ k => collect k tbl
  | Ecase _ _ cl =>
      (fix go (cl : list (ctor_tag * exp)) tbl :=
         match cl with
         | [] => tbl
         | (_, e) :: cl => go cl (collect e tbl)
         end) cl tbl
  | Efun B k => collect k (collect_fd B tbl)
  | Eapp _ _ _ | Eprim_val _ _ _ | Eprim _ _ _ _ | Ehalt _ => tbl
  end
with collect_fd (B : fundefs) (tbl : M.t entry) : M.t entry :=
  match B with
  | Fcons f w xs e B =>
      let tbl := if exposedb w then tbl else add_mask w (map (is_free e) xs) tbl in
      collect_fd B (collect e tbl)
  | Fnil => tbl
  end.

Definition masks (e : exp) : M.t (list bool) :=
  M.map_filter1 (fun o : entry => o) (collect e (M.empty _)).

(** * The transformation *)

Section Transform.

  Variable (L : M.t (list bool)).

  Definition dpe_args {A} (w : web) (ys : list A) : list A :=
    if keeps (sel_L L) w then ys
    else match L ! w with Some bs => live_args ys bs | None => ys end.

  Fixpoint dpe (e : exp) : exp :=
    match e with
    | Econstr x w t ys k =>
        let k' := dpe k in if is_free k' x then Econstr x w t ys k' else k'
    | Eproj x w t n y k =>
        let k' := dpe k in if is_free k' x then Eproj x w t n y k' else k'
    | Ecase x w cl =>
        Ecase x w ((fix go (cl : list (ctor_tag * exp)) :=
                      match cl with
                      | [] => []
                      | (c, e) :: cl => (c, dpe e) :: go cl
                      end) cl)
    | Eletapp x f w ys k => Eletapp x f w (dpe_args w ys) (dpe k)
    | Efun B k =>
        let k' := dpe k in if existsb (is_free k') (bnames B) then Efun (dpe_fd B) k' else k'
    | Eapp f w ys => Eapp f w (dpe_args w ys)
    | Eprim_val x p k => Eprim_val x p k
    | Eprim x p ys k => Eprim x p ys k
    | Ehalt x => Ehalt x
    end
  with dpe_fd (B : fundefs) : fundefs :=
    match B with
    | Fcons f w xs e B => Fcons f w (dpe_args w xs) (dpe e) (dpe_fd B)
    | Fnil => Fnil
    end.

End Transform.

Definition dpe_top (e : exp) : exp := dpe (masks e) e.

(** * The transformation inhabits the relation *)

(** Properties of the functions of an expression *)
Fixpoint all_funs (P : web -> list var -> exp -> Prop) (e : exp) : Prop :=
  match e with
  | Econstr _ _ _ _ k | Eproj _ _ _ _ _ k | Eletapp _ _ _ _ k => all_funs P k
  | Ecase _ _ cl =>
      (fix go (cl : list (ctor_tag * exp)) :=
         match cl with
         | [] => True
         | (_, e) :: cl => all_funs P e /\ go cl
         end) cl
  | Efun B k => all_funs_fd P B /\ all_funs P k
  | Eapp _ _ _ | Eprim_val _ _ _ | Eprim _ _ _ _ | Ehalt _ => True
  end
with all_funs_fd (P : web -> list var -> exp -> Prop) (B : fundefs) : Prop :=
  match B with
  | Fcons f w xs e B => P w xs e /\ all_funs P e /\ all_funs_fd P B
  | Fnil => True
  end.

Section Correct.

  Variables (L : M.t (list bool)) (Gb : nat).

  Definition mask_ok (w : web) (xs : list var) (e : exp) : Prop :=
    forall bs, exposedb w = false -> L ! w = Some bs ->
               length bs = length xs /\ Disjoint _ (FromList (dead_args xs bs)) (occurs_free e).

  Lemma dpe_args_keeps {A} w (ys : list A) : keeps (sel_L L) w = true -> dpe_args L w ys = ys.
  Proof. unfold dpe_args. intros H; rewrite H; reflexivity. Qed.

  Lemma dpe_args_sel {A} w (ys : list A) :
    keeps (sel_L L) w = false -> exists bs, exposedb w = false /\ L ! w = Some bs /\ dpe_args L w ys = live_args ys bs.
  Proof.
    unfold dpe_args. intros H. rewrite H. apply keeps_internal in H. destruct H as [Hw Hs].
    unfold sel_L in Hs. destruct (L ! w) as [bs |] eqn:HL; [| discriminate ].
    eexists; eauto.
  Qed.

  Lemma dpe_trans :
    (forall e, all_funs mask_ok e -> esize e <= Gb -> trans L Gb (esize e) e (dpe L e)) /\
    (forall B, all_funs_fd mask_ok B -> fsize B <= Gb -> trans_fundefs L Gb B (dpe_fd L B)).
  Proof.
    eapply exp_fundefs_ind; simpl.
    - (* Econstr *)
      intros x w t ys e IH Hok Hs.
      specialize (IH Hok ltac:(lia)).
      destruct (is_free (dpe L e) x) eqn:Hx.
      + constructor. eapply trans_weaken; [ eassumption | lia ].
      + econstructor; [ eassumption | lia | eapply is_free_false; eassumption ].
    - (* Ecase [] *)
      intros. constructor.
    - (* Ecase (_ :: _) *)
      intros x w cl c e IHe IHcl [Hok Hokcl] Hs. simpl in IHcl.
      constructor.
      + eapply trans_weaken; [ eapply IHe; [ eassumption | lia ] | lia ].
      + eapply trans_weaken; [ eapply IHcl; [ eassumption | lia ] | lia ].
    - (* Eproj *)
      intros x w t n y e IH Hok Hs.
      specialize (IH Hok ltac:(lia)).
      destruct (is_free (dpe L e) x) eqn:Hx.
      + constructor. eapply trans_weaken; [ eassumption | lia ].
      + econstructor; [ eassumption | lia | eapply is_free_false; eassumption ].
    - (* Eletapp *)
      intros x f w ys e IH Hok Hs.
      specialize (IH Hok ltac:(lia)).
      destruct (keeps (sel_L L) w) eqn:Hk.
      + rewrite dpe_args_keeps; [| eassumption ].
        constructor; [ eassumption | eapply trans_weaken; [ eassumption | lia ] ].
      + edestruct (dpe_args_sel w ys Hk) as (bs & Hw & HL & ->).
        econstructor; [ eassumption | eassumption | eapply trans_weaken; [ eassumption | lia ] ].
    - (* Efun *)
      intros B e IHB IHe [HokB Hoke] Hs.
      specialize (IHe Hoke ltac:(lia)). specialize (IHB HokB ltac:(lia)).
      destruct (existsb (is_free (dpe L e)) (bnames B)) eqn:Hb.
      + constructor; [ eassumption | eapply trans_weaken; [ eassumption | lia ] ].
      + econstructor; [ eassumption | lia |].
        constructor. intros z Hz. destruct Hz as [z Hz1 Hz2].
        eapply is_free_spec in Hz2.
        assert (Hc : existsb (is_free (dpe L e)) (bnames B) = true).
        { eapply existsb_exists. eexists; split; [ eapply name_in_bnames; eassumption | eassumption ]. }
        congruence.
    - (* Eapp *)
      intros f w ys Hok Hs.
      destruct (keeps (sel_L L) w) eqn:Hk.
      + rewrite dpe_args_keeps; [| eassumption ]. constructor; eassumption.
      + edestruct (dpe_args_sel w ys Hk) as (bs & Hw & HL & ->). econstructor; eassumption.
    - (* Eprim_val *) intros. constructor.
    - (* Eprim *) intros. constructor.
    - (* Ehalt *) intros. constructor.
    - (* Fcons *)
      intros f w xs e B IHe IHB (Hm & Hoke & HokB) Hs.
      specialize (IHe Hoke ltac:(lia)). specialize (IHB HokB ltac:(lia)).
      destruct (keeps (sel_L L) w) eqn:Hk.
      + rewrite dpe_args_keeps; [| eassumption ].
        constructor; [ eassumption | eapply trans_weaken; [ eassumption | lia ] | eassumption ].
      + edestruct (dpe_args_sel w xs Hk) as (bs & Hw & HL & ->).
        destruct (Hm bs Hw HL) as [Hlen Hdis].
        econstructor; eauto.
        * eapply trans_weaken; [ eassumption | lia ].
        * eapply Disjoint_Included_r; [| eassumption ]. eapply trans_occurs_free; eassumption.
    - (* Fnil *) intros. constructor.
  Qed.

End Correct.

(** ** The analysis computes correct masks *)

Fixpoint bools_le (l1 l2 : list bool) : Prop :=
  match l1, l2 with
  | b1 :: l1, b2 :: l2 => (b1 = true -> b2 = true) /\ bools_le l1 l2
  | [], [] => True
  | _, _ => False
  end.

(** Order on the entries of the table; [Some None] (conflict) is the top *)
Definition entry_le (a b : option entry) : Prop :=
  match a, b with
  | None, _ => True
  | Some None, Some None => True
  | Some None, _ => False
  | Some (Some _), Some None => True
  | Some (Some m1), Some (Some m2) => length m1 = length m2 /\ bools_le m1 m2
  | Some (Some _), None => False
  end.

Lemma bools_le_refl l : bools_le l l.
Proof. induction l; simpl; eauto. Qed.

Lemma bools_le_trans l1 l2 l3 : bools_le l1 l2 -> bools_le l2 l3 -> bools_le l1 l3.
Proof.
  revert l2 l3; induction l1; intros [| b2 l2] [| b3 l3]; simpl; intuition eauto.
Qed.

Lemma entry_le_refl a : entry_le a a.
Proof. destruct a as [[m |] |]; simpl; eauto using bools_le_refl. Qed.

Lemma entry_le_trans a b c : entry_le a b -> entry_le b c -> entry_le a c.
Proof.
  destruct a as [[m1 |] |], b as [[m2 |] |], c as [[m3 |] |]; simpl; intuition eauto using bools_le_trans; congruence.
Qed.

Lemma join_bool_length l1 l2 : length l1 = length l2 -> length (join_bool l1 l2) = length l1.
Proof. revert l2; induction l1; intros [| b l2]; simpl; intros H; inv H; eauto. Qed.

Lemma join_bool_le_l l1 l2 : length l1 = length l2 -> bools_le l1 (join_bool l1 l2).
Proof.
  revert l2; induction l1; intros [| b l2]; simpl; intros H; inv H; eauto.
  split; eauto. intros ->. reflexivity.
Qed.

Lemma join_bool_le_r l1 l2 : length l1 = length l2 -> bools_le l2 (join_bool l1 l2).
Proof.
  revert l2; induction l1; intros [| b l2]; simpl; intros H; inv H; eauto.
  split; eauto. intros ->. apply orb_true_r.
Qed.

Lemma add_mask_mono w m tbl w' : entry_le (tbl ! w') ((add_mask w m tbl) ! w').
Proof.
  unfold add_mask. destruct (peq w' w); subst.
  - destruct (tbl ! w) as [[m' |] |] eqn:Hw.
    + destruct (Nat.eqb_spec (length m') (length m)); rewrite M.gss; simpl; eauto.
      split; [ symmetry; eapply join_bool_length; eassumption | eapply join_bool_le_l; eassumption ].
    + rewrite Hw. simpl. eauto.
    + simpl. eauto.
  - destruct (tbl ! w) as [[m' |] |] eqn:Hw;
      [ destruct (Nat.eqb (length m') (length m)) | |]; rewrite ?M.gso; eauto using entry_le_refl.
Qed.

Lemma add_mask_covers w m tbl : entry_le (Some (Some m)) ((add_mask w m tbl) ! w).
Proof.
  unfold add_mask. destruct (tbl ! w) as [[m' |] |] eqn:Hw.
  - destruct (Nat.eqb_spec (length m') (length m)); rewrite M.gss; simpl; eauto.
    split; [ rewrite join_bool_length; eauto | eapply join_bool_le_r; eassumption ].
  - rewrite Hw. simpl. eauto.
  - rewrite M.gss. simpl. split; eauto using bools_le_refl.
Qed.

Lemma collect_mono :
  (forall e tbl w, entry_le (tbl ! w) ((collect e tbl) ! w)) /\
  (forall B tbl w, entry_le (tbl ! w) ((collect_fd B tbl) ! w)).
Proof.
  eapply exp_fundefs_ind; simpl; intros; eauto using entry_le_refl.
  - eapply entry_le_trans; [| eapply H0 ]. eauto.
  - eapply entry_le_trans; [ eapply H | eapply H0 ].
  - eapply entry_le_trans; [| eapply H0 ]. eapply entry_le_trans; [| eapply H ].
    destruct (exposedb w); [ eapply entry_le_refl | eapply add_mask_mono ].
Qed.

Definition covered (T : M.t entry) (w : web) (xs : list var) (e : exp) : Prop :=
  exposedb w = false -> entry_le (Some (Some (map (is_free e) xs))) (T ! w).

Lemma collect_covers :
  (forall e tbl T, (forall w, entry_le ((collect e tbl) ! w) (T ! w)) -> all_funs (covered T) e) /\
  (forall B tbl T, (forall w, entry_le ((collect_fd B tbl) ! w) (T ! w)) -> all_funs_fd (covered T) B).
Proof.
  eapply exp_fundefs_ind.
  - intros x w t ys e He tbl T HT. exact (He tbl T HT).
  - intros. exact I.
  - intros x w cl c e He Hcl tbl T HT. split.
    + eapply He. intros w'. eapply entry_le_trans; [ exact (proj1 collect_mono (Ecase x w cl) (collect e tbl) w') | exact (HT w') ].
    + exact (Hcl (collect e tbl) T HT).
  - intros x w t n y e He tbl T HT. exact (He tbl T HT).
  - intros x f w ys e He tbl T HT. exact (He tbl T HT).
  - intros B e HB He tbl T HT. split.
    + eapply HB with (tbl := tbl). intros w'. eapply entry_le_trans; [| exact (HT w') ]. exact (proj1 collect_mono e (collect_fd B tbl) w').
    + exact (He (collect_fd B tbl) T HT).
  - intros. exact I.
  - intros. exact I.
  - intros. exact I.
  - intros. exact I.
  - intros f w xs e B He HB tbl T HT. split; [| split ].
    + intros Hw. pose proof (HT w) as HTw. simpl in HTw. rewrite Hw in HTw.
      eapply entry_le_trans; [ eapply add_mask_covers |].
      eapply entry_le_trans; [ eapply (proj1 collect_mono) |].
      eapply entry_le_trans; [ eapply (proj2 collect_mono) | exact HTw ].
    + eapply He with (tbl := if exposedb w then tbl else add_mask w (map (is_free e) xs) tbl).
      intros w'. eapply entry_le_trans; [ eapply (proj2 collect_mono) | exact (HT w') ].
    + exact (HB _ T HT).
  - intros. exact I.
Qed.

Lemma dead_args_not_free e xs bs z :
  bools_le (map (is_free e) xs) bs -> List.In z (dead_args xs bs) -> ~ occurs_free e z.
Proof.
  revert bs; induction xs as [| x xs IH]; intros [| b bs] Hle Hin; simpl in *; try contradiction.
  destruct Hle as [Hb Hle]. destruct b.
  - eapply IH; eauto.
  - destruct Hin as [-> | Hin]; [| eapply IH; eauto ].
    intros Hc. eapply is_free_spec in Hc. specialize (Hb Hc). congruence.
Qed.

Lemma all_funs_mono (P Q : web -> list var -> exp -> Prop) :
  (forall w xs e, P w xs e -> Q w xs e) ->
  (forall e, all_funs P e -> all_funs Q e) /\ (forall B, all_funs_fd P B -> all_funs_fd Q B).
Proof. intros HPQ. eapply exp_fundefs_ind; simpl; intros; intuition eauto. Qed.

Lemma masks_ok e : all_funs (mask_ok (masks e)) e.
Proof.
  set (T := collect e (M.empty _)).
  pose proof (proj1 collect_covers e (M.empty _) T (fun w => entry_le_refl _)) as Hc.
  assert (Himp : forall w xs body, covered T w xs body -> mask_ok (masks e) w xs body).
  { intros w xs body Hcov bs Hw HL. unfold masks in HL. fold T in HL. rewrite M.gmap_filter1 in HL.
    specialize (Hcov Hw). destruct (T ! w) as [[m |] |]; simpl in *; try congruence. inv HL.
    destruct Hcov as [Hlen Hle]. split; [ rewrite <- Hlen, length_map; reflexivity |].
    constructor. intros z Hz. destruct Hz as [z Hz1 Hz2]. eapply dead_args_not_free; eassumption. }
  exact (proj1 (all_funs_mono _ _ Himp) e Hc).
Qed.

(** * Correctness of the implementation *)

Theorem dpe_top_trans e : trans (masks e) (esize e) (esize e) e (dpe_top e).
Proof. eapply dpe_trans; [ eapply masks_ok | lia ]. Qed.

Section Top.

  Variable (cenv : term.ctor_env).

  (** The implementation preserves the behavior of closed programs, including
      divergence. *)
  Theorem dpe_top_refines e : closed_exp e -> refines cenv value_ref e (dpe_top e).
  Proof. intros Hc. eapply dpe_refines; [ eassumption | | eapply dpe_top_trans ]. lia. Qed.

  (** And it is in the λweb relation, for any postconditions of the
      [dead_bound] family. *)
  Theorem dpe_top_correct e :
    E_web cenv (dead_bound (esize e) (esize e)) (dead_bound (esize e) (esize e)) e (dpe_top e).
  Proof.
    eapply (E_web_dpe_dead cenv (masks e) (esize e) (dead_bound (esize e) (esize e)) (fun n => dead_bound n (esize e)));
      [ lia | eapply dpe_top_trans ].
  Qed.

End Top.
