(* An implementation of arity raising, and the proof that it inhabits the
   relation of ar.v.

   - The transformation [ar] follows the relation: it tracks the scoped
     environment of the known shapes, projects the fields of the flattened
     arguments of the calls of the webs in the map into fresh variables, and
     rebuilds the flattened parameters on entry.  Fresh names come from a
     counter that starts above every variable of the program.
   - The checker [ar_ok] checks the side conditions of the relation (every
     flattened argument has a known shape; the transformed functions have
     distinct parameters and the right arity), and [La_ok] that the map only
     flattens internal constructors with fields.  They are proven sound.
   - The analysis [ar_analyze] computes, for every internal web, the shapes
     passed at each position by all the calls of the web.  Flattened
     parameters of the enclosing functions have known shapes, so the analysis
     is iterated; it is not proven correct: the top level uses the most
     precise result that the checkers accept, and otherwise transforms no
     web. *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics set_util.
From CertiRocq.LambdaWeb Require Import syntax semantics exposed post select indep bound comp dpe dpe_impl
     cp cp_impl ar.
From CertiRocq.LambdaWeb Require fixpoint.

Import ListNotations.

(** * Variables of a program *)

(** All the variables of a program are at most [m] *)
Fixpoint vle (m : var) (e : exp) : Prop :=
  match e with
  | Econstr x _ _ ys e => (x <= m)%positive /\ Forall (fun y => (y <= m)%positive) ys /\ vle m e
  | Ecase x _ cl =>
      (x <= m)%positive /\
      (fix vle_br (cl : list (ctor_tag * exp)) :=
         match cl with
         | [] => True
         | (_, e) :: cl => vle m e /\ vle_br cl
         end) cl
  | Eproj x _ _ _ y e => (x <= m)%positive /\ (y <= m)%positive /\ vle m e
  | Eletapp x f _ ys e =>
      (x <= m)%positive /\ (f <= m)%positive /\ Forall (fun y => (y <= m)%positive) ys /\ vle m e
  | Efun B e => vle_fd m B /\ vle m e
  | Eapp f _ ys => (f <= m)%positive /\ Forall (fun y => (y <= m)%positive) ys
  | Eprim_val x _ e => (x <= m)%positive /\ vle m e
  | Eprim x _ ys e => (x <= m)%positive /\ Forall (fun y => (y <= m)%positive) ys /\ vle m e
  | Ehalt x => (x <= m)%positive
  end
with vle_fd (m : var) (B : fundefs) : Prop :=
  match B with
  | Fcons f _ xs e B => (f <= m)%positive /\ Forall (fun x => (x <= m)%positive) xs /\ vle m e /\ vle_fd m B
  | Fnil => True
  end.

Definition maxl (l : list var) (acc : var) : var := fold_left Pos.max l acc.

Fixpoint maxv (e : exp) (acc : var) : var :=
  match e with
  | Econstr x _ _ ys e => maxv e (maxl ys (Pos.max x acc))
  | Ecase x _ cl =>
      (fix maxv_br (cl : list (ctor_tag * exp)) (acc : var) :=
         match cl with
         | [] => acc
         | (_, e) :: cl => maxv_br cl (maxv e acc)
         end) cl (Pos.max x acc)
  | Eproj x _ _ _ y e => maxv e (Pos.max x (Pos.max y acc))
  | Eletapp x f _ ys e => maxv e (maxl ys (Pos.max x (Pos.max f acc)))
  | Efun B e => maxv e (maxv_fd B acc)
  | Eapp f _ ys => maxl ys (Pos.max f acc)
  | Eprim_val x _ e => maxv e (Pos.max x acc)
  | Eprim x _ ys e => maxv e (maxl ys (Pos.max x acc))
  | Ehalt x => Pos.max x acc
  end
with maxv_fd (B : fundefs) (acc : var) : var :=
  match B with
  | Fcons f _ xs e B => maxv_fd B (maxv e (maxl xs (Pos.max f acc)))
  | Fnil => acc
  end.

(** * Fresh names *)

Fixpoint fresh_n (c : positive) (n : nat) : list var * positive :=
  match n with
  | O => ([], c)
  | S n => let '(l, c') := fresh_n (Pos.succ c) n in (c :: l, c')
  end.

Fixpoint fresh_for (ss : list (option shape)) (c : positive) : list (list var) * positive :=
  match ss with
  | [] => ([], c)
  | Some (_, n, _) :: ss =>
      let '(zs, c) := fresh_n c n in
      let '(zss, c) := fresh_for ss c in
      (zs :: zss, c)
  | None :: ss => let '(zss, c) := fresh_for ss c in ([] :: zss, c)
  end.

(** * The transformation and its checker *)

Fixpoint shape_okb (K : M.t shape) (ys : list var) (ss : list (option shape)) : bool :=
  match ys, ss with
  | y :: ys', Some s :: ss' =>
      match K ! y, s with
      | Some (w', n', c'), (w, n, c) => web_eqb w' w && Nat.eqb n' n && Pos.eqb c' c
      | None, _ => false
      end && shape_okb K ys' ss'
  | _ :: ys', None :: ss' => shape_okb K ys' ss'
  | _, _ => true
  end.

Lemma shape_okb_spec K ys ss : shape_okb K ys ss = true -> shape_ok K ys ss.
Proof.
  revert ss; induction ys as [| y ys IH]; intros [| [[[w n] c] |] ss] H; simpl in *; eauto.
  destruct (K ! y) as [[[w' n'] c'] |]; [| discriminate ].
  apply andb_true_iff in H as [H1 H2]. apply andb_true_iff in H1 as [H1 H3].
  apply andb_true_iff in H1 as [H1 H4].
  apply web_eqb_eq in H1. apply Nat.eqb_eq in H4. apply Pos.eqb_eq in H3. subst. split; eauto.
Qed.

Section Transform.

  Variable (La : WM.t (list (option shape))).

  Definition ar_ss (w : web) : list (option shape) :=
    match WM.get w La with Some ss => ss | None => [] end.

  Fixpoint ar (K : M.t shape) (e : exp) (c : positive) : exp * positive :=
    match e with
    | Econstr x w t ys k =>
        let '(k', c) := ar (M.set x (w, length ys, t) K) k c in (Econstr x w t ys k', c)
    | Eproj x w t n y k => let '(k', c) := ar (M.remove x K) k c in (Eproj x w t n y k', c)
    | Ecase x w cl =>
        let '(cl', c) :=
          (fix ar_br (cl : list (ctor_tag * exp)) (c : positive) :=
             match cl with
             | [] => ([], c)
             | (t, e) :: cl =>
                 let '(e', c) := ar K e c in
                 let '(cl', c) := ar_br cl c in
                 ((t, e') :: cl', c)
             end) cl c in
        (Ecase x w cl', c)
    | Eletapp x f w ys k =>
        if keeps (sel_L La) w then
          let '(k', c) := ar (M.remove x K) k c in (Eletapp x f w ys k', c)
        else
          let ss := ar_ss w in
          let '(zss, c) := fresh_for ss c in
          let '(k', c) := ar (M.remove x K) k c in
          (proj_args ys ss zss (Eletapp x f w (flat_vars ys ss zss) k'), c)
    | Efun B k =>
        let K' := remove_names B K in
        let '(B', c) := ar_fd K' B c in
        let '(k', c) := ar K' k c in
        (Efun B' k', c)
    | Eapp f w ys =>
        if keeps (sel_L La) w then (Eapp f w ys, c)
        else
          let ss := ar_ss w in
          let '(zss, c) := fresh_for ss c in
          (proj_args ys ss zss (Eapp f w (flat_vars ys ss zss)), c)
    | Eprim_val x p k => let '(k', c) := ar (M.remove x K) k c in (Eprim_val x p k', c)
    | Eprim x p ys k => let '(k', c) := ar (M.remove x K) k c in (Eprim x p ys k', c)
    | Ehalt x => (Ehalt x, c)
    end
  with ar_fd (K : M.t shape) (B : fundefs) (c : positive) : fundefs * positive :=
    match B with
    | Fcons f w xs e B =>
        if keeps (sel_L La) w then
          let '(e', c) := ar (param_shapes xs [] K) e c in
          let '(B', c) := ar_fd K B c in
          (Fcons f w xs e' B', c)
        else
          let ss := ar_ss w in
          let '(yss, c) := fresh_for ss c in
          let '(e', c) := ar (param_shapes xs ss K) e c in
          let '(B', c) := ar_fd K B c in
          (Fcons f w (flat_vars xs ss yss) (rebuild xs ss yss e') B', c)
    | Fnil => (Fnil, c)
    end.

  Fixpoint ar_ok (K : M.t shape) (e : exp) : bool :=
    match e with
    | Econstr x w t ys k => ar_ok (M.set x (w, length ys, t) K) k
    | Eproj x w t n y k => ar_ok (M.remove x K) k
    | Ecase x w cl =>
        (fix go (cl : list (ctor_tag * exp)) :=
           match cl with
           | [] => true
           | (c, e) :: cl => ar_ok K e && go cl
           end) cl
    | Eletapp x f w ys k =>
        (keeps (sel_L La) w ||
         (Nat.eqb (length ys) (length (ar_ss w)) && shape_okb K ys (ar_ss w))) &&
        ar_ok (M.remove x K) k
    | Efun B k => ar_ok_fd (remove_names B K) B && ar_ok (remove_names B K) k
    | Eapp f w ys =>
        keeps (sel_L La) w || (Nat.eqb (length ys) (length (ar_ss w)) && shape_okb K ys (ar_ss w))
    | Eprim_val x _ k | Eprim x _ _ k => ar_ok (M.remove x K) k
    | Ehalt _ => true
    end
  with ar_ok_fd (K : M.t shape) (B : fundefs) : bool :=
    match B with
    | Fcons f w xs e B =>
        (if keeps (sel_L La) w then ar_ok (param_shapes xs [] K) e
         else Nat.eqb (length (ar_ss w)) (length xs) && nodupb xs &&
              ar_ok (param_shapes xs (ar_ss w) K) e) && ar_ok_fd K B
    | Fnil => true
    end.

  (** The map only flattens internal constructors with fields *)
  Definition info_okb (s : option shape) : bool :=
    match s with Some (wc, n, _) => negb (exposedb wc) && Nat.ltb 0 n | None => true end.

  Definition La_ok : bool := forallb (fun '(_, ss) => forallb info_okb ss) (WM_elements La).

End Transform.

(** * Properties of the fresh names *)

Lemma fresh_n_spec c n :
  length (fst (fresh_n c n)) = n /\ NoDup (fst (fresh_n c n)) /\
  (forall z, List.In z (fst (fresh_n c n)) -> (c <= z)%positive /\ (z < snd (fresh_n c n))%positive) /\
  (c <= snd (fresh_n c n))%positive.
Proof.
  revert c. induction n as [| n IH]; intros c; simpl.
  - split; [ reflexivity | split; [ constructor | split; [ intros _ [] | lia ] ] ].
  - destruct (IH (Pos.succ c)) as (H1 & H2 & H3 & H4).
    destruct (fresh_n (Pos.succ c) n) as [l c'] eqn:Hf. simpl in *.
    split; [ congruence | split; [| split ] ].
    + constructor; [| exact H2 ]. intros Hc. destruct (H3 _ Hc). lia.
    + intros z [-> | Hz]; [ lia |]. destruct (H3 _ Hz). lia.
    + lia.
Qed.

Lemma fresh_for_spec ss c :
  Forall2 fresh_ok ss (fst (fresh_for ss c)) /\ NoDup (concat (fst (fresh_for ss c))) /\
  (forall z, List.In z (concat (fst (fresh_for ss c))) -> (c <= z)%positive /\ (z < snd (fresh_for ss c))%positive) /\
  (c <= snd (fresh_for ss c))%positive.
Proof.
  revert c. induction ss as [| s ss IH]; intros c; simpl.
  - split; [ constructor | split; [ constructor | split; [ intros _ [] | lia ] ] ].
  - destruct s as [[[wc n] t] |].
    + destruct (fresh_n_spec c n) as (Hn1 & Hn2 & Hn3 & Hn4).
      destruct (fresh_n c n) as [zs c1] eqn:Hf. simpl in *.
      destruct (IH c1) as (H1 & H2 & H3 & H4).
      destruct (fresh_for ss c1) as [zss c2] eqn:Hff. simpl in *.
      split; [ constructor; eauto | split; [| split ] ].
      * eapply NoDup_app_intro; eauto. intros z Hz Hc. destruct (Hn3 _ Hz). destruct (H3 _ Hc). lia.
      * intros z Hz. apply in_app_or in Hz as [Hz | Hz]; [ destruct (Hn3 _ Hz) | destruct (H3 _ Hz) ]; lia.
      * lia.
    + destruct (IH c) as (H1 & H2 & H3 & H4).
      destruct (fresh_for ss c) as [zss c2] eqn:Hff. simpl in *.
      split; [ constructor; [ reflexivity | eauto ] | split; [ exact H2 | split; [ exact H3 | exact H4 ] ] ].
Qed.

(** * Variables *)

Lemma Forall_le_mono (l : list var) m m' :
  Forall (fun y => (y <= m)%positive) l -> (m <= m')%positive -> Forall (fun y => (y <= m')%positive) l.
Proof. intros H Hm. induction H; constructor; [ eapply Pos.le_trans; eassumption | eauto ]. Qed.

Lemma Forall_le_In (l : list var) m z : Forall (fun y => (y <= m)%positive) l -> List.In z l -> (z <= m)%positive.
Proof. intros H Hz. eapply Forall_forall in H; eauto. Qed.

Lemma vle_fv m :
  (forall e, vle m e -> forall z, occurs_free e z -> (z <= m)%positive) /\
  (forall B, vle_fd m B -> forall z, occurs_free_fundefs B z -> (z <= m)%positive).
Proof.
  eapply exp_fundefs_ind; simpl; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
  - apply occurs_free_Econstr in H1. destruct H1 as [z' Hz | z' [Hz _]]; [ eapply Forall_le_In; eauto | eauto ].
  - apply occurs_free_Ecase_nil in H0. inv H0. assumption.
  - apply occurs_free_Ecase_cons in H2. destruct H2 as [z' Hz | z' [z'' Hz | z'' Hz]]; [ inv Hz; assumption | eauto |].
    eapply H0; [ split; eauto | exact Hz ].
  - apply occurs_free_Eproj in H1. destruct H1 as [z' Hz | z' [Hz _]]; [ inv Hz; assumption | eauto ].
  - apply occurs_free_Eletapp in H1. destruct H1 as [z' [z'' Hz | z'' Hz] | z' [Hz _]];
      [ inv Hz; assumption | eapply Forall_le_In; eauto | eauto ].
  - apply occurs_free_Efun in H2. destruct H2 as [z' Hz | z' [Hz _]]; eauto.
  - apply occurs_free_Eapp in H0. destruct H0 as [z' Hz | z' Hz]; [ eapply Forall_le_In; eauto | inv Hz; assumption ].
  - apply occurs_free_Eprim_val in H1. destruct H1 as [Hz _]. eauto.
  - apply occurs_free_Eprim in H1. destruct H1 as [z' Hz | z' [Hz _]]; [ eapply Forall_le_In; eauto | eauto ].
  - apply occurs_free_Ehalt in H0. inv H0. assumption.
  - match goal with Hz : occurs_free_fundefs (Fcons _ _ _ _ _) _ |- _ =>
      apply occurs_free_fundefs_Fcons in Hz; destruct Hz as [z' [Hz _] | z' [Hz _]]; eauto end.
  - match goal with Hz : occurs_free_fundefs Fnil _ |- _ => apply occurs_free_fundefs_Fnil in Hz; inv Hz end.
Qed.

Lemma maxl_ge (l : list var) acc : (acc <= maxl l acc)%positive /\ Forall (fun y => (y <= maxl l acc)%positive) l.
Proof.
  unfold maxl. revert acc. induction l as [| a l IH]; intros acc; simpl; [ split; [ lia | constructor ] |].
  destruct (IH (Pos.max acc a)) as [H1 H2]. split; [ lia | constructor; [ lia | exact H2 ] ].
Qed.

Lemma vle_mono :
  (forall e m m', vle m e -> (m <= m')%positive -> vle m' e) /\
  (forall B m m', vle_fd m B -> (m <= m')%positive -> vle_fd m' B).
Proof.
  eapply exp_fundefs_ind; simpl; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; eauto using Forall_le_mono; try lia.
  - eapply (H0 m m'); [ split; eauto | eassumption ].
Qed.

Lemma vle_maxv :
  (forall e acc, (acc <= maxv e acc)%positive /\ vle (maxv e acc) e) /\
  (forall B acc, (acc <= maxv_fd B acc)%positive /\ vle_fd (maxv_fd B acc) B).
Proof.
  eapply exp_fundefs_ind; simpl; intros.
  - destruct (maxl_ge ys (Pos.max x acc)) as [H1 H2]. destruct (H (maxl ys (Pos.max x acc))) as [H3 H4].
    split; [ lia | split; [ lia | split; [ eapply Forall_le_mono; eauto | exact H4 ] ] ].
  - split; [ lia | split; [ lia | exact I ] ].
  - destruct (H (Pos.max x acc)) as [H1 H2].
    specialize (H0 (maxv e (Pos.max x acc))).
    rewrite (Pos.max_r x (maxv e (Pos.max x acc))) in H0 by lia.
    destruct H0 as [H3 [H4 H5]].
    split; [ lia | split; [ lia | split; [ eapply (proj1 vle_mono); eauto | exact H5 ] ] ].
  - destruct (H (Pos.max x (Pos.max y acc))) as [H1 H2]. split; [ lia | split; [ lia | split; [ lia | exact H2 ] ] ].
  - destruct (maxl_ge ys (Pos.max x (Pos.max f acc))) as [H1 H2]. destruct (H (maxl ys (Pos.max x (Pos.max f acc)))) as [H3 H4].
    split; [ lia | split; [ lia | split; [ lia | split; [ eapply Forall_le_mono; eauto | exact H4 ] ] ] ].
  - destruct (H acc) as [H1 H2]. destruct (H0 (maxv_fd B acc)) as [H3 H4].
    split; [ lia | split; [ eapply (proj2 vle_mono); eauto | exact H4 ] ].
  - destruct (maxl_ge ys (Pos.max f acc)) as [H1 H2]. split; [ lia | split; [ lia | exact H2 ] ].
  - destruct (H (Pos.max x acc)) as [H1 H2]. split; [ lia | split; [ lia | exact H2 ] ].
  - destruct (maxl_ge ys (Pos.max x acc)) as [H1 H2]. destruct (H (maxl ys (Pos.max x acc))) as [H3 H4].
    split; [ lia | split; [ lia | split; [ eapply Forall_le_mono; eauto | exact H4 ] ] ].
  - split; lia.
  - destruct (maxl_ge xs (Pos.max f acc)) as [H1 H2]. destruct (H (maxl xs (Pos.max f acc))) as [H3 H4].
    destruct (H0 (maxv e (maxl xs (Pos.max f acc)))) as [H5 H6].
    split; [ lia | split; [ lia | split; [ eapply Forall_le_mono; eauto; lia | split; [ eapply (proj1 vle_mono); eauto | exact H6 ] ] ] ].
  - split; [ lia | exact I ].
Qed.

(** * The checker is sound *)

Lemma La_ok_spec La w ss : La_ok La = true -> WM.get w La = Some ss -> Forall info_ok ss /\ Forall pos_ok ss.
Proof.
  intros H Hw. eapply WM_elements_correct in Hw. unfold La_ok in H.
  eapply forallb_forall in H; [| exact Hw ]. simpl in H.
  split; eapply Forall_forall; intros s Hs; eapply forallb_forall in H; eauto;
    destruct s as [[[wc n] c] |]; simpl in *; try exact I;
    apply andb_true_iff in H as [H1 H2]; [ apply negb_true_iff in H1; exact H1 | apply Nat.ltb_lt in H2; exact H2 ].
Qed.

Lemma ar_ss_sel La w : keeps (sel_L La) w = false -> exposedb w = false /\ WM.get w La = Some (ar_ss La w).
Proof.
  intros H. apply keeps_internal in H. destruct H as [Hw Hs]. split; [ eassumption |].
  unfold sel_L, ar_ss in *. destruct (WM.get w La); congruence.
Qed.

Section Sound.

  Variables (La : WM.t (list (option shape))) (m : var).
  Hypothesis (HLa : La_ok La = true).

  Lemma fresh_disjoint_fv zss c e e' K :
    (forall z, List.In z (concat zss) -> (c <= z)%positive) -> (m < c)%positive -> vle m e ->
    trans La K e e' -> forall S, Disjoint _ (FromList (concat zss)) (occurs_free e' \\ S).
  Proof.
    intros Hz Hc Hv Ht S. constructor. intros z Hin. inv Hin. destruct H0 as [H0 _].
    eapply (proj1 (trans_occurs_free La)) in H0; [| eassumption ].
    eapply (proj1 (vle_fv m)) in H0; [| eassumption ]. specialize (Hz _ H). lia.
  Qed.

  Lemma ar_trans :
    (forall e K c, ar_ok La K e = true -> vle m e -> (m < c)%positive ->
                   trans La K e (fst (ar La K e c)) /\ (c <= snd (ar La K e c))%positive) /\
    (forall B K c, ar_ok_fd La K B = true -> vle_fd m B -> (m < c)%positive ->
                   trans_fundefs La K B (fst (ar_fd La K B c)) /\ (c <= snd (ar_fd La K B c))%positive).
  Proof.
    eapply exp_fundefs_ind.
    - (* Econstr *)
      intros x w t ys e IH K c Hok Hv Hlt. simpl in *. destruct Hv as (Hx & Hys & He).
      specialize (IH _ c Hok He Hlt). destruct (ar La _ e c) as [e' c'] eqn:Hk. simpl in *.
      destruct IH as [Ht Hc]. split; [ constructor; exact Ht | exact Hc ].
    - (* Ecase [] *)
      intros. simpl. split; [ constructor | lia ].
    - (* Ecase (_ :: _) *)
      intros x w cl t e IHe IHcl K c Hok Hv Hlt. simpl in Hok, Hv. apply andb_true_iff in Hok as [Hoke Hokcl].
      destruct Hv as (Hx & He & Hcl).
      specialize (IHe _ c Hoke He Hlt). simpl.
      destruct (ar La K e c) as [e' c1] eqn:Hk. simpl in IHe. destruct IHe as [Hte Hc1].
      specialize (IHcl K c1 Hokcl (conj Hx Hcl) ltac:(lia)). simpl in IHcl.
      match goal with |- context [ ?F cl c1 ] => destruct (F cl c1) as [cl' c2] eqn:Hcl' end.
      simpl in *. destruct IHcl as [Htcl Hc2]. split; [ constructor; eauto | lia ].
    - (* Eproj *)
      intros x w t n y e IH K c Hok Hv Hlt. simpl in *. destruct Hv as (Hx & Hy & He).
      specialize (IH _ c Hok He Hlt). destruct (ar La _ e c) as [e' c'] eqn:Hk. simpl in *.
      destruct IH as [Ht Hc]. split; [ constructor; exact Ht | exact Hc ].
    - (* Eletapp *)
      intros x f w ys e IH K c Hok Hv Hlt. simpl in *. destruct Hv as (Hx & Hf & Hys & He).
      apply andb_true_iff in Hok as [Hcall Hok].
      destruct (keeps (sel_L La) w) eqn:Hkeep.
      + specialize (IH _ c Hok He Hlt). destruct (ar La _ e c) as [e' c'] eqn:Hk. simpl in *.
        destruct IH as [Ht Hc]. split; [ constructor; eauto | exact Hc ].
      + destruct (ar_ss_sel La w Hkeep) as [Hw HL]. simpl in Hcall.
        apply andb_true_iff in Hcall as [Hlen Hsh]. apply Nat.eqb_eq in Hlen.
        destruct (La_ok_spec La w _ HLa HL) as [Hinfo Hpos].
        destruct (fresh_for_spec (ar_ss La w) c) as (Hf1 & Hf2 & Hf3 & Hf4).
        destruct (fresh_for (ar_ss La w) c) as [zss c1] eqn:Hfr. simpl in *.
        specialize (IH _ c1 Hok He ltac:(lia)). destruct (ar La _ e c1) as [e' c2] eqn:Hk. simpl in *.
        destruct IH as [Ht Hc]. split; [| lia ].
        econstructor; eauto using shape_okb_spec.
        * constructor. intros z Hin. inv Hin. destruct (Hf3 _ H) as [Hz _].
          inv H0; [ inv H1; lia |]. eapply Forall_le_In in H1; [| exact Hys ]. lia.
        * eapply fresh_disjoint_fv; eauto. intros z Hz. eapply Hf3. exact Hz.
    - (* Efun *)
      intros B e IHB IHe K c Hok Hv Hlt. simpl in *. destruct Hv as (HB & He).
      apply andb_true_iff in Hok as [HokB Hoke].
      specialize (IHB _ c HokB HB Hlt). destruct (ar_fd La _ B c) as [B' c1] eqn:HkB. simpl in *.
      destruct IHB as [HtB Hc1].
      specialize (IHe _ c1 Hoke He ltac:(lia)). destruct (ar La _ e c1) as [e' c2] eqn:Hk. simpl in *.
      destruct IHe as [Hte Hc2]. split; [ constructor; eauto | lia ].
    - (* Eapp *)
      intros f w ys K c Hok Hv Hlt. simpl in *. destruct Hv as (Hf & Hys).
      destruct (keeps (sel_L La) w) eqn:Hkeep.
      + simpl. split; [ constructor; eauto | lia ].
      + destruct (ar_ss_sel La w Hkeep) as [Hw HL]. simpl in Hok.
        apply andb_true_iff in Hok as [Hlen Hsh]. apply Nat.eqb_eq in Hlen.
        destruct (La_ok_spec La w _ HLa HL) as [Hinfo Hpos].
        destruct (fresh_for_spec (ar_ss La w) c) as (Hf1 & Hf2 & Hf3 & Hf4).
        destruct (fresh_for (ar_ss La w) c) as [zss c1] eqn:Hfr. simpl in *.
        split; [| lia ].
        econstructor; eauto using shape_okb_spec.
        constructor. intros z Hin. inv Hin. destruct (Hf3 _ H) as [Hz _].
        inv H0; [ inv H1; lia |]. eapply Forall_le_In in H1; [| exact Hys ]. lia.
    - (* Eprim_val *)
      intros x p e IH K c Hok Hv Hlt. simpl in *. destruct Hv as (Hx & He).
      specialize (IH _ c Hok He Hlt). destruct (ar La _ e c) as [e' c'] eqn:Hk. simpl in *.
      destruct IH as [Ht Hc]. split; [ constructor; exact Ht | exact Hc ].
    - (* Eprim *)
      intros x p ys e IH K c Hok Hv Hlt. simpl in *. destruct Hv as (Hx & Hys & He).
      specialize (IH _ c Hok He Hlt). destruct (ar La _ e c) as [e' c'] eqn:Hk. simpl in *.
      destruct IH as [Ht Hc]. split; [ constructor; exact Ht | exact Hc ].
    - (* Ehalt *) intros. simpl. split; [ constructor | lia ].
    - (* Fcons *)
      intros f w xs e B IHe IHB K c Hok Hv Hlt. simpl in *. destruct Hv as (Hfm & Hxs & He & HB).
      apply andb_true_iff in Hok as [Hokf HokB].
      destruct (keeps (sel_L La) w) eqn:Hkeep.
      + specialize (IHe _ c Hokf He Hlt). destruct (ar La _ e c) as [e' c1] eqn:Hk. simpl in *.
        destruct IHe as [Hte Hc1].
        specialize (IHB K c1 HokB HB ltac:(lia)). destruct (ar_fd La K B c1) as [B' c2] eqn:HkB. simpl in *.
        destruct IHB as [HtB Hc2]. split; [ constructor; eauto | lia ].
      + destruct (ar_ss_sel La w Hkeep) as [Hw HL].
        apply andb_true_iff in Hokf as [Hokf Hoke]. apply andb_true_iff in Hokf as [Hlen Hnd].
        apply Nat.eqb_eq in Hlen.
        destruct (La_ok_spec La w _ HLa HL) as [Hinfo Hpos].
        destruct (fresh_for_spec (ar_ss La w) c) as (Hf1 & Hf2 & Hf3 & Hf4).
        destruct (fresh_for (ar_ss La w) c) as [yss c1] eqn:Hfr. simpl in *.
        specialize (IHe _ c1 Hoke He ltac:(lia)). destruct (ar La _ e c1) as [e' c2] eqn:Hk. simpl in *.
        destruct IHe as [Hte Hc2].
        specialize (IHB K c2 HokB HB ltac:(lia)). destruct (ar_fd La K B c2) as [B' c3] eqn:HkB. simpl in *.
        destruct IHB as [HtB Hc3]. split; [| lia ].
        econstructor; eauto.
        * eapply NoDup_app_intro; [ eapply nodupb_spec; eassumption | eassumption |].
          intros z Hz Hc'. destruct (Hf3 _ Hc') as [Hz' _]. eapply Forall_le_In in Hz; [| exact Hxs ]. lia.
        * constructor. intros z Hin. inv Hin. destruct (Hf3 _ H) as [Hz _].
          eapply (proj1 (trans_occurs_free La)) in H0; [| eassumption ].
          eapply (proj1 (vle_fv m)) in H0; [| eassumption ]. lia.
    - (* Fnil *) intros. simpl. split; [ constructor | lia ].
  Qed.

End Sound.

(** With no selected web, the checkers always succeed. *)
Lemma ar_ok_empty :
  (forall e K, ar_ok (WM.empty _) K e = true) /\ (forall B K, ar_ok_fd (WM.empty _) K B = true).
Proof.
  assert (Hk : forall w, keeps (sel_L (WM.empty (list (option shape)))) w = true).
  { intros w. unfold keeps, sel_L. rewrite WM.gempty. apply orb_true_r. }
  eapply exp_fundefs_ind; simpl; intros; rewrite ?Hk; simpl;
    repeat match goal with
           | [ IH : forall K, ?g K ?x = true |- context [ ?g ?K' ?x ] ] => rewrite IH
           end; eauto.
Qed.

Lemma La_ok_empty : La_ok (WM.empty (list (option shape))) = true.
Proof.
  unfold La_ok. eapply forallb_forall. intros [w ss] Hin.
  unfold WM_elements in Hin. apply in_map_iff in Hin as ([p a] & _ & Hin).
  apply M.elements_complete in Hin. rewrite M.gempty in Hin. congruence.
Qed.

(** * The analysis *)

Definition shape_eqb (s1 s2 : shape) : bool :=
  let '(w1, n1, c1) := s1 in let '(w2, n2, c2) := s2 in web_eqb w1 w2 && Nat.eqb n1 n2 && Pos.eqb c1 c2.

Definition meet_sh (a b : option shape) : option shape :=
  match a, b with
  | Some s, Some s' => if shape_eqb s s' then Some s else None
  | _, _ => None
  end.

Fixpoint meet_shs (l1 l2 : list (option shape)) : list (option shape) :=
  match l1, l2 with
  | a :: l1, b :: l2 => meet_sh a b :: meet_shs l1 l2
  | _, _ => []
  end.

(** Only internal constructors with fields are flattened *)
Definition usable (s : option shape) : option shape :=
  match s with
  | Some (wc, n, c) => if negb (exposedb wc) && Nat.ltb 0 n then s else None
  | None => None
  end.

Definition add_call_sh (w : web) (info : list (option shape)) (tbl : WM.t (option (list (option shape)))) :=
  match WM.get w tbl with
  | None => WM.set w (Some info) tbl
  | Some None => tbl
  | Some (Some info') =>
      if Nat.eqb (length info') (length info) then WM.set w (Some (meet_shs info' info)) tbl
      else WM.set w None tbl
  end.

Section Analysis.

  (** The shapes of the previous round, for the parameters *)
  Variable (Lprev : WM.t (list (option shape))).

  Definition prev_ss (w : web) : list (option shape) :=
    if exposedb w then [] else match WM.get w Lprev with Some ss => ss | None => [] end.

  Definition atables : Type := (WM.t (option (list (option shape))) * WM.t (option nat))%type.

  Fixpoint collect_ar (K : M.t shape) (e : exp) (t : atables) : atables :=
    match e with
    | Econstr x w c ys k => collect_ar (M.set x (w, length ys, c) K) k t
    | Eproj x _ _ _ _ k => collect_ar (M.remove x K) k t
    | Ecase _ _ cl =>
        (fix go (cl : list (ctor_tag * exp)) t :=
           match cl with
           | [] => t
           | (_, e) :: cl => go cl (collect_ar K e t)
           end) cl t
    | Eletapp x f w ys k =>
        let t := if exposedb w then t else (add_call_sh w (map (fun y => usable (K ! y)) ys) (fst t), snd t) in
        collect_ar (M.remove x K) k t
    | Efun B k => collect_ar (remove_names B K) k (collect_ar_fd (remove_names B K) B t)
    | Eapp f w ys => if exposedb w then t else (add_call_sh w (map (fun y => usable (K ! y)) ys) (fst t), snd t)
    | Eprim_val x _ k | Eprim x _ _ k => collect_ar (M.remove x K) k t
    | Ehalt _ => t
    end
  with collect_ar_fd (K : M.t shape) (B : fundefs) (t : atables) : atables :=
    match B with
    | Fcons f w xs e B =>
        let t := if exposedb w then t else (fst t, add_fun w xs (snd t)) in
        collect_ar_fd K B (collect_ar (param_shapes xs (prev_ss w) K) e t)
    | Fnil => t
    end.

  Definition ar_analyze (e : exp) : WM.t (list (option shape)) :=
    let '(calls, funs) := collect_ar (M.empty _) e (WM.empty _, WM.empty _) in
    M.map_filter1 (fun o => o)
      (M.map (fun p (ce : option (list (option shape))) => let w := web_of_index p in
                match ce, WM.get w funs with
                | Some ss, Some (Some n) =>
                    if Nat.eqb n (length ss) && negb (exposedb w) &&
                       existsb (fun o : option shape => match o with Some _ => true | None => false end) ss
                    then Some ss else None
                | _, _ => None
                end) calls).

End Analysis.

Fixpoint ar_analyze_n (n : nat) (e : exp) : WM.t (list (option shape)) :=
  match n with
  | 0 => WM.empty _
  | S n => ar_analyze (ar_analyze_n n e) e
  end.

(** The shapes of the known-constructor fixpoint of [fixpoint.v]: a
    position is flattened if it always receives the same internal
    constructor with fields, and the record is only projected
    ([fixpoint.escaping]), so that rebuilding it on entry does not
    allocate once the projections are resolved *)
Definition ar_fix (e : exp) : list (WM.t (list (option shape))) :=
  match fixpoint.param_cons e with
  | Some P =>
      let sh (v : fixpoint.cval) : option shape :=
        match v with fixpoint.CCon wc c n => usable (Some (wc, n, c)) | _ => None end in
      let flat w i := match WM.get w P with
                      | Some vs => match sh (nth i vs fixpoint.CBot) with Some _ => true | None => false end
                      | None => false
                      end in
      match fixpoint.escaping e flat with
      | Some Esc =>
          [fold_left (fun La '(w, vs) =>
                        let es := match WM.get w Esc with Some es => es | None => [] end in
                        let ss := fixpoint.imap (fun i v => if nth i es true then None else sh v) vs in
                        if existsb (fun o : option shape => match o with Some _ => true | None => false end) ss
                        then WM.set w ss La else La) (WM_elements P) (WM.empty _)]
      | None => []
      end
  | None => []
  end.

(** The first map that the checkers accept: the fixpoint, or else the
    rounds of the local analysis *)
Definition ar_choose (e : exp) : WM.t (list (option shape)) :=
  let cands := ar_fix e ++ [ar_analyze_n 3 e; ar_analyze_n 2 e; ar_analyze_n 1 e] in
  match find (fun La => La_ok La && ar_ok La (M.empty _) e) cands with
  | Some La => La
  | None => WM.empty _
  end.

Lemma ar_choose_ok e : La_ok (ar_choose e) = true /\ ar_ok (ar_choose e) (M.empty _) e = true.
Proof.
  unfold ar_choose.
  destruct (find (fun La => La_ok La && ar_ok La (M.empty _) e) _) eqn:Hf.
  - eapply find_some in Hf. apply andb_true_iff. apply Hf.
  - split; [ eapply La_ok_empty | eapply ar_ok_empty ].
Qed.

Definition ar_top (e : exp) : exp :=
  fst (ar (ar_choose e) (M.empty _) e (Pos.succ (maxv e 1%positive))).

(** * Correctness of the implementation *)

Theorem ar_top_trans e : trans (ar_choose e) (M.empty _) e (ar_top e).
Proof.
  destruct (ar_choose_ok e) as [HLa Hok]. unfold ar_top.
  eapply (proj1 (ar_trans (ar_choose e) (maxv e 1%positive) HLa)); [ exact Hok | | lia ].
  eapply (proj1 vle_maxv).
Qed.

Section Top.

  Variable (cenv : term.ctor_env).

  Theorem ar_top_correct e : E_web cenv (dead_bound 0 0) (dead_bound 0 0) e (ar_top e).
  Proof.
    eapply (E_web_ar cenv (ar_choose e) (dead_bound 0 0) (Hprops := dead_bound_properties cenv 0 0 (le_n _)));
      [ eapply dead_bound_target_step | eapply ar_top_trans ].
  Qed.

End Top.
