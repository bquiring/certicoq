(* An implementation of DPE with dead-binding elimination, and the proof that
   it inhabits the relation of dpe.v.

   - The analysis is the liveness fixpoint of [fixpoint.v]: a parameter is
     dead if it is only passed on to dead positions.  The simpler [masks]
     (a parameter is live if it occurs free in the body) is the fallback.
     A checker validates the masks: the dead parameters of a function must
     not occur in its transformed body.
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
From CertiRocq.LambdaWeb Require fixpoint.

Import ListNotations.

(** * Preliminaries *)

(** Mutual induction on expressions and bundles *)


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

Definition add_mask (w : web) (m : list bool) (tbl : WM.t entry) : WM.t entry :=
  match WM.get w tbl with
  | None => WM.set w (Some m) tbl
  | Some None => tbl
  | Some (Some m') =>
      if Nat.eqb (length m') (length m) then WM.set w (Some (join_bool m' m)) tbl
      else WM.set w None tbl
  end.

Fixpoint collect (e : exp) (tbl : WM.t entry) : WM.t entry :=
  match e with
  | Econstr _ _ _ _ k | Eproj _ _ _ _ _ k | Eletapp _ _ _ _ k
  | Eprim_val _ _ k | Eprim _ _ _ k => collect k tbl
  | Ecase _ _ cl =>
      (fix go (cl : list (ctor_tag * exp)) tbl :=
         match cl with
         | [] => tbl
         | (_, e) :: cl => go cl (collect e tbl)
         end) cl tbl
  | Efun B k => collect k (collect_fd B tbl)
  | Eapp _ _ _ | Ehalt _ => tbl
  end
with collect_fd (B : fundefs) (tbl : WM.t entry) : WM.t entry :=
  match B with
  | Fcons f w xs e B =>
      let tbl := if exposedb w then tbl else add_mask w (map (is_free e) xs) tbl in
      collect_fd B (collect e tbl)
  | Fnil => tbl
  end.

Definition masks (e : exp) : WM.t (list bool) :=
  M.map_filter1 (fun o : entry => o) (collect e (WM.empty _)).

(** * The transformation *)

Section Transform.

  Variable (L : WM.t (list bool)).

  Definition dpe_args {A} (w : web) (ys : list A) : list A :=
    if keeps (sel_L L) w then ys
    else match WM.get w L with Some bs => live_args ys bs | None => ys end.

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
    | Eprim_val x p k => Eprim_val x p (dpe k)
    | Eprim x p ys k => Eprim x p ys (dpe k)
    | Ehalt x => Ehalt x
    end
  with dpe_fd (B : fundefs) : fundefs :=
    match B with
    | Fcons f w xs e B => Fcons f w (dpe_args w xs) (dpe e) (dpe_fd B)
    | Fnil => Fnil
    end.

End Transform.


(** * The transformation inhabits the relation *)

(** Properties of the functions of an expression *)
Fixpoint all_funs (P : web -> list var -> exp -> Prop) (e : exp) : Prop :=
  match e with
  | Econstr _ _ _ _ k | Eproj _ _ _ _ _ k | Eletapp _ _ _ _ k
  | Eprim_val _ _ k | Eprim _ _ _ k => all_funs P k
  | Ecase _ _ cl =>
      (fix go (cl : list (ctor_tag * exp)) :=
         match cl with
         | [] => True
         | (_, e) :: cl => all_funs P e /\ go cl
         end) cl
  | Efun B k => all_funs_fd P B /\ all_funs P k
  | Eapp _ _ _ | Ehalt _ => True
  end
with all_funs_fd (P : web -> list var -> exp -> Prop) (B : fundefs) : Prop :=
  match B with
  | Fcons f w xs e B => P w xs e /\ all_funs P e /\ all_funs_fd P B
  | Fnil => True
  end.

Section Correct.

  Variables (L : WM.t (list bool)) (Gb : nat).

  (** The dead parameters of a function do not occur in its transformed
      body (a parameter only passed on to dead positions is dead) *)
  Definition mask_ok (w : web) (xs : list var) (e : exp) : Prop :=
    forall bs, exposedb w = false -> WM.get w L = Some bs ->
               length bs = length xs /\ Disjoint _ (FromList (dead_args xs bs)) (occurs_free (dpe L e)).

  Lemma dpe_args_keeps {A} w (ys : list A) : keeps (sel_L L) w = true -> dpe_args L w ys = ys.
  Proof. unfold dpe_args. intros H; rewrite H; reflexivity. Qed.

  Lemma dpe_args_sel {A} w (ys : list A) :
    keeps (sel_L L) w = false -> exists bs, exposedb w = false /\ WM.get w L = Some bs /\ dpe_args L w ys = live_args ys bs.
  Proof.
    unfold dpe_args. intros H. rewrite H. apply keeps_internal in H. destruct H as [Hw Hs].
    unfold sel_L in Hs. destruct (WM.get w L) as [bs |] eqn:HL; [| discriminate ].
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
    - (* Eprim_val *)
      intros x p e IH Hok Hs. constructor. eapply trans_weaken; [ eapply IH; [ eassumption | lia ] | lia ].
    - (* Eprim *)
      intros x p ys e IH Hok Hs. constructor. eapply trans_weaken; [ eapply IH; [ eassumption | lia ] | lia ].
    - (* Ehalt *) intros. constructor.
    - (* Fcons *)
      intros f w xs e B IHe IHB (Hm & Hoke & HokB) Hs.
      specialize (IHe Hoke ltac:(lia)). specialize (IHB HokB ltac:(lia)).
      destruct (keeps (sel_L L) w) eqn:Hk.
      + rewrite dpe_args_keeps; [| eassumption ].
        constructor; [ eassumption | eapply trans_weaken; [ eassumption | lia ] | eassumption ].
      + edestruct (dpe_args_sel w xs Hk) as (bs & Hw & HL & ->).
        destruct (Hm bs Hw HL) as [Hlen Hdis].
        econstructor; eauto. eapply trans_weaken; [ eassumption | lia ].
    - (* Fnil *) intros. constructor.
  Qed.

End Correct.

(** ** Checking the masks

    The masks come from an untrusted analysis, the liveness fixpoint of
    [fixpoint.v], or else from [masks]; the transformation uses the first
    that the checker accepts. *)

Definition mok (L : WM.t (list bool)) (w : web) (xs : list var) (e : exp) : bool :=
  if exposedb w then true
  else match WM.get w L with
       | Some bs => Nat.eqb (length bs) (length xs) &&
                    forallb (fun x => negb (is_free (dpe L e) x)) (dead_args xs bs)
       | None => true
       end.

Lemma mok_spec L w xs e : mok L w xs e = true -> mask_ok L w xs e.
Proof.
  unfold mok, mask_ok. intros H bs Hw HL. rewrite Hw, HL in H.
  apply andb_true_iff in H as [Hlen Hd]. apply Nat.eqb_eq in Hlen. split; [ exact Hlen |].
  constructor. intros z Hz. destruct Hz as [z Hz1 Hz2].
  eapply forallb_forall in Hd; [| exact Hz1 ]. apply negb_true_iff in Hd.
  eapply is_free_false; eassumption.
Qed.

Fixpoint mchk (L : WM.t (list bool)) (e : exp) : bool :=
  match e with
  | Econstr _ _ _ _ k | Eproj _ _ _ _ _ k | Eletapp _ _ _ _ k
  | Eprim_val _ _ k | Eprim _ _ _ k => mchk L k
  | Ecase _ _ cl =>
      (fix go (cl : list (ctor_tag * exp)) :=
         match cl with
         | [] => true
         | (_, e) :: cl => mchk L e && go cl
         end) cl
  | Efun B k => mchk_fd L B && mchk L k
  | Eapp _ _ _ | Ehalt _ => true
  end
with mchk_fd (L : WM.t (list bool)) (B : fundefs) : bool :=
  match B with
  | Fcons f w xs e B => mok L w xs e && mchk L e && mchk_fd L B
  | Fnil => true
  end.

Lemma mchk_spec L :
  (forall e, mchk L e = true -> all_funs (mask_ok L) e) /\
  (forall B, mchk_fd L B = true -> all_funs_fd (mask_ok L) B).
Proof.
  eapply exp_fundefs_ind; simpl; intros;
    repeat match goal with
           | [ H : (_ && _) = true |- _ ] => apply andb_true_iff in H; destruct H
           end; intuition eauto using mok_spec.
Qed.

Lemma all_funs_mono (P Q : web -> list var -> exp -> Prop) :
  (forall w xs e, P w xs e -> Q w xs e) ->
  (forall e, all_funs P e -> all_funs Q e) /\ (forall B, all_funs_fd P B -> all_funs_fd Q B).
Proof. intros HPQ. eapply exp_fundefs_ind; simpl; intros; intuition eauto. Qed.

Lemma all_funs_true :
  (forall e, all_funs (fun _ _ _ => True) e) /\ (forall B, all_funs_fd (fun _ _ _ => True) B).
Proof. eapply exp_fundefs_ind; simpl; intros; intuition eauto. Qed.

Definition choose_masks (e : exp) : WM.t (list bool) :=
  let cands := match fixpoint.live_masks e with Some L => [L] | None => [] end ++ [masks e] in
  match find (fun L => mchk L e) cands with
  | Some L => L
  | None => WM.empty _
  end.

Lemma choose_masks_ok e : all_funs (mask_ok (choose_masks e)) e.
Proof.
  unfold choose_masks.
  destruct (find (fun L => mchk L e) _) eqn:Hf.
  - eapply find_some in Hf. eapply (proj1 (mchk_spec _)). apply Hf.
  - assert (Hm : forall w xs e', (fun _ _ _ => True) w xs e' -> mask_ok (WM.empty _) w xs e').
    { intros w xs e' _ bs _ HL. rewrite WM.gempty in HL. discriminate. }
    exact (proj1 (all_funs_mono _ _ Hm) e (proj1 all_funs_true e)).
Qed.

Definition dpe_top (e : exp) : exp := dpe (choose_masks e) e.

(** * Correctness of the implementation *)

Theorem dpe_top_trans e : trans (choose_masks e) (esize e) (esize e) e (dpe_top e).
Proof. eapply dpe_trans; [ eapply choose_masks_ok | lia ]. Qed.

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
    eapply (E_web_dpe_dead cenv (choose_masks e) (esize e) (dead_bound (esize e) (esize e)) (fun n => dead_bound n (esize e)));
      [ lia | eapply dpe_top_trans ].
  Qed.

End Top.
