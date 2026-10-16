(* An implementation of DPE with dead-binding elimination, and the proof that
   it inhabits the relation of dpe.v.

   - The analysis is the liveness fixpoint of [fixpoint.v]: a parameter is
     dead if it is only passed on to dead positions.  A checker validates
     the masks: the dead parameters of a function must not occur in its
     transformed body.
   - The transformation [dpe] drops the dead parameters of the functions of
     the webs in the map and the corresponding arguments of their calls, and
     drops the [Econstr], [Eproj] and [Efun] bindings whose variables are
     dead in the transformed continuation.
   - The budget of removed bindings is the size of the program.
   - [dpe] and the checker [mchk] are the reference; [dpe_fv] computes
     both, with the free variables of the result, in one pass, and is the
     one that runs (asking for the free variables of each continuation is
     quadratic). *)

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

(** ** The implementation that runs *)

Definition set_of (l : list var) : PS.t := fold_left (fun s x => PS.add x s) l PS.empty.

Lemma set_of_spec l z : PS.In z (set_of l) <-> List.In z l.
Proof.
  unfold set_of.
  assert (H : forall s, PS.In z (fold_left (fun s x => PS.add x s) l s) <-> PS.In z s \/ List.In z l).
  { induction l as [| x l IH]; intros s; simpl; [ tauto |].
    rewrite IH, PS.add_spec. split; [ intros [[H | H] | H]; auto | intros [H | [H | H]]; auto ]. }
  rewrite H. split; [ intros [H1 | H1]; [ apply PS.empty_spec in H1; contradiction | exact H1 ] | right; assumption ].
Qed.

Lemma forallb_ext' {A} (f g : A -> bool) l : (forall x, f x = g x) -> forallb f l = forallb g l.
Proof. intros H. induction l; simpl; [ reflexivity | rewrite H, IHl; reflexivity ]. Qed.

Lemma existsb_ext' {A} (f g : A -> bool) l : (forall x, f x = g x) -> existsb f l = existsb g l.
Proof. intros H. induction l; simpl; [ reflexivity | rewrite H, IHl; reflexivity ]. Qed.

(** [S] is the set [E] *)
Definition fv_ok (S : PS.t) (E : Ensemble var) : Prop := forall z, PS.In z S <-> E z.

Lemma same_iff (A B : Ensemble var) z : A <--> B -> (A z <-> B z).
Proof. intros [H1 H2]. split; [ apply H1 | apply H2 ]. Qed.

Lemma Union_iff (A B : Ensemble var) z : (A :|: B) z <-> A z \/ B z.
Proof. split; [ intros [z' H | z' H]; auto | intros [H | H]; [ left | right ]; exact H ]. Qed.

Lemma Setminus_iff (A B : Ensemble var) z : (A \\ B) z <-> A z /\ ~ B z.
Proof. split; [ intros [H1 H2]; auto | intros [H1 H2]; constructor; auto ]. Qed.

Lemma Singleton_iff (x z : var) : [set x] z <-> z = x.
Proof. split; [ intros H; inv H; reflexivity | intros ->; constructor ]. Qed.

Lemma mem_fv S e x : fv_ok S (occurs_free e) -> PS.mem x S = is_free e x.
Proof.
  intros H. destruct (PS.mem x S) eqn:E1, (is_free e x) eqn:E2; auto.
  - apply PS.mem_spec, H, is_free_spec in E1. congruence.
  - apply is_free_spec, H, PS.mem_spec in E2. congruence.
Qed.

Section Fv.

  Variable (L : WM.t (list bool)).

  Definition mok_fv (w : web) (xs : list var) (fe : PS.t) : bool :=
    if exposedb w then true
    else match WM.get w L with
         | Some bs => Nat.eqb (length bs) (length xs) && forallb (fun x => negb (PS.mem x fe)) (dead_args xs bs)
         | None => true
         end.

  Fixpoint dpe_fv (e : exp) : exp * PS.t * bool :=
    match e with
    | Econstr x w t ys k =>
        let '(k', fk, ok) := dpe_fv k in
        if PS.mem x fk then (Econstr x w t ys k', PS.union (set_of ys) (PS.remove x fk), ok) else (k', fk, ok)
    | Eproj x w t n y k =>
        let '(k', fk, ok) := dpe_fv k in
        if PS.mem x fk then (Eproj x w t n y k', PS.add y (PS.remove x fk), ok) else (k', fk, ok)
    | Ecase x w cl =>
        let '(cl', fs, ok) :=
          (fix go (cl : list (ctor_tag * exp)) : list (ctor_tag * exp) * PS.t * bool :=
             match cl with
             | [] => ([], PS.empty, true)
             | (c, e) :: cl =>
                 let '(e', fe, ok1) := dpe_fv e in
                 let '(cl', fcl, ok2) := go cl in
                 ((c, e') :: cl', PS.union fe fcl, ok1 && ok2)
             end) cl in
        (Ecase x w cl', PS.add x fs, ok)
    | Eletapp x f w ys k =>
        let '(k', fk, ok) := dpe_fv k in
        let ys' := dpe_args L w ys in
        (Eletapp x f w ys' k', PS.add f (PS.union (set_of ys') (PS.remove x fk)), ok)
    | Efun B k =>
        let '(k', fk, ok) := dpe_fv k in
        let '(B', fB, nB, okB) := dpe_fv_fd B in
        if existsb (fun f => PS.mem f fk) (bnames B) then (Efun B' k', PS.union fB (PS.diff fk nB), okB && ok)
        else (k', fk, okB && ok)
    | Eapp f w ys => let ys' := dpe_args L w ys in (Eapp f w ys', PS.add f (set_of ys'), true)
    | Eprim_val x p k => let '(k', fk, ok) := dpe_fv k in (Eprim_val x p k', PS.remove x fk, ok)
    | Eprim x p ys k =>
        let '(k', fk, ok) := dpe_fv k in (Eprim x p ys k', PS.union (set_of ys) (PS.remove x fk), ok)
    | Ehalt x => (Ehalt x, PS.singleton x, true)
    end
  with dpe_fv_fd (B : fundefs) : fundefs * PS.t * PS.t * bool :=
    match B with
    | Fcons f w xs e B =>
        let '(e', fe, oke) := dpe_fv e in
        let '(B', fB, nB, okB) := dpe_fv_fd B in
        let xs' := dpe_args L w xs in
        (Fcons f w xs' e' B',
         PS.union (PS.diff fe (PS.add f (PS.union (set_of xs') nB))) (PS.remove f fB),
         PS.add f nB,
         mok_fv w xs fe && oke && okB)
    | Fnil => (Fnil, PS.empty, PS.empty, true)
    end.

  Lemma mok_fv_eq w xs e fe : fv_ok fe (occurs_free (dpe L e)) -> mok_fv w xs fe = mok L w xs e.
  Proof.
    intros H. unfold mok_fv, mok. destruct (exposedb w); [ reflexivity |].
    destruct (WM.get w L) as [bs |]; [| reflexivity ]. f_equal.
    apply forallb_ext'. intros x. rewrite (mem_fv _ _ x H). reflexivity.
  Qed.

  Ltac fv_simpl :=
    repeat first [ rewrite PS.union_spec | rewrite PS.remove_spec | rewrite PS.add_spec | rewrite PS.diff_spec
                 | rewrite PS.singleton_spec | rewrite set_of_spec | rewrite Union_iff | rewrite Setminus_iff
                 | rewrite Singleton_iff ].

  Lemma dpe_fv_correct :
    (forall e, let '(e', fe, ok) := dpe_fv e in e' = dpe L e /\ fv_ok fe (occurs_free e') /\ ok = mchk L e) /\
    (forall B, let '(B', fB, nB, ok) := dpe_fv_fd B in
               B' = dpe_fd L B /\ fv_ok fB (occurs_free_fundefs B') /\ fv_ok nB (name_in_fundefs B') /\
               ok = mchk_fd L B).
  Proof.
    eapply exp_fundefs_ind; simpl.
    - (* Econstr *)
      intros x w t ys k IH. destruct (dpe_fv k) as [[k' fk] ok]. destruct IH as (-> & Hf & ->).
      rewrite (mem_fv _ _ x Hf). destruct (is_free (dpe L k) x); [| auto ].
      split; [ reflexivity | split; [| reflexivity ] ].
      intros z. rewrite (same_iff _ _ z (occurs_free_Econstr _ _ _ _ _)). fv_simpl. rewrite (Hf z).
      unfold FromList, Ensembles.In. tauto.
    - (* Ecase [] *)
      intros x w. split; [ reflexivity | split; [| reflexivity ] ].
      intros z. rewrite (same_iff _ _ z (occurs_free_Ecase_nil _ _)). fv_simpl.
      split; [ intros [H | H]; [ exact H | apply PS.empty_spec in H; contradiction ] | intros H; left; exact H ].
    - (* Ecase (_ :: _) *)
      intros x w cl c e IHe IHcl. simpl in IHcl.
      destruct (dpe_fv e) as [[e' fe] ok1]. destruct IHe as (-> & Hfe & ->).
      match type of IHcl with
      | context [?G cl] =>
          let T := type of (G cl) in
          lazymatch T with
          | (list (ctor_tag * exp) * PS.t * bool)%type => destruct (G cl) as [[cl' fcl] ok2]
          end
      end.
      destruct IHcl as (Hcl & Hfcl & Hok). injection Hcl as Hcl.
      split; [ rewrite Hcl; reflexivity | split ].
      + intros z. rewrite (same_iff _ _ z (occurs_free_Ecase_cons _ _ _ _ _)). fv_simpl.
        rewrite (Hfe z). rewrite <- (Hfcl z). fv_simpl. tauto.
      + rewrite Hok. reflexivity.
    - (* Eproj *)
      intros x w t n y k IH. destruct (dpe_fv k) as [[k' fk] ok]. destruct IH as (-> & Hf & ->).
      rewrite (mem_fv _ _ x Hf). destruct (is_free (dpe L k) x); [| auto ].
      split; [ reflexivity | split; [| reflexivity ] ].
      intros z. rewrite (same_iff _ _ z (occurs_free_Eproj _ _ _ _ _ _)). fv_simpl. rewrite (Hf z). tauto.
    - (* Eletapp *)
      intros x f w ys k IH. destruct (dpe_fv k) as [[k' fk] ok]. destruct IH as (-> & Hf & ->).
      split; [ reflexivity | split; [| reflexivity ] ].
      intros z. rewrite (same_iff _ _ z (occurs_free_Eletapp _ _ _ _ _)). fv_simpl. rewrite (Hf z).
      unfold FromList, Ensembles.In. tauto.
    - (* Efun *)
      intros B k IHB IHk. destruct (dpe_fv k) as [[k' fk] ok]. destruct IHk as (-> & Hf & ->).
      destruct (dpe_fv_fd B) as [[[B' fB] nB] okB]. destruct IHB as (-> & HfB & HnB & ->).
      assert (Hex : existsb (fun f => PS.mem f fk) (bnames B) = existsb (is_free (dpe L k)) (bnames B))
        by (apply existsb_ext'; intros f; apply mem_fv; exact Hf).
      rewrite Hex. destruct (existsb (is_free (dpe L k)) (bnames B)).
      + split; [ reflexivity | split; [| reflexivity ] ].
        intros z. rewrite (same_iff _ _ z (occurs_free_Efun _ _)). fv_simpl. rewrite (HfB z), (Hf z), (HnB z). tauto.
      + split; [ reflexivity | split; [ exact Hf | reflexivity ] ].
    - (* Eapp *)
      intros f w ys. split; [ reflexivity | split; [| reflexivity ] ].
      intros z. rewrite (same_iff _ _ z (occurs_free_Eapp _ _ _)). fv_simpl.
      unfold FromList, Ensembles.In. tauto.
    - (* Eprim_val *)
      intros x p k IH. destruct (dpe_fv k) as [[k' fk] ok]. destruct IH as (-> & Hf & ->).
      split; [ reflexivity | split; [| reflexivity ] ].
      intros z. rewrite (same_iff _ _ z (occurs_free_Eprim_val _ _ _)). fv_simpl. rewrite (Hf z). tauto.
    - (* Eprim *)
      intros x p ys k IH. destruct (dpe_fv k) as [[k' fk] ok]. destruct IH as (-> & Hf & ->).
      split; [ reflexivity | split; [| reflexivity ] ].
      intros z. rewrite (same_iff _ _ z (occurs_free_Eprim _ _ _ _)). fv_simpl. rewrite (Hf z).
      unfold FromList, Ensembles.In. tauto.
    - (* Ehalt *)
      intros x. split; [ reflexivity | split; [| reflexivity ] ].
      intros z. rewrite (same_iff _ _ z (occurs_free_Ehalt _)). fv_simpl. tauto.
    - (* Fcons *)
      intros f w xs e B IHe IHB. destruct (dpe_fv e) as [[e' fe] oke]. destruct IHe as (-> & Hfe & ->).
      destruct (dpe_fv_fd B) as [[[B' fB] nB] okB]. destruct IHB as (-> & HfB & HnB & ->).
      split; [ reflexivity | split; [| split ] ].
      + intros z. rewrite (same_iff _ _ z (occurs_free_fundefs_Fcons _ _ _ _ _)). fv_simpl.
        rewrite (Hfe z), (HfB z), (HnB z). unfold FromList, Ensembles.In. tauto.
      + intros z. simpl. fv_simpl. rewrite (HnB z). tauto.
      + rewrite (mok_fv_eq _ _ _ _ Hfe). reflexivity.
    - (* Fnil *)
      split; [ reflexivity | split; [| split; [| reflexivity ] ] ].
      + intros z. rewrite (same_iff _ _ z occurs_free_fundefs_Fnil).
        split; [ intros H; apply PS.empty_spec in H; contradiction | intros H; inv H ].
      + intros z. simpl. split; [ intros H; apply PS.empty_spec in H; contradiction | intros H; inv H ].
  Qed.

  Lemma dpe_fv_fst e : fst (fst (dpe_fv e)) = dpe L e.
  Proof. pose proof (proj1 dpe_fv_correct e) as H. destruct (dpe_fv e) as [[e' fe] ok]. apply H. Qed.

  Lemma dpe_fv_ok e : snd (dpe_fv e) = mchk L e.
  Proof. pose proof (proj1 dpe_fv_correct e) as H. destruct (dpe_fv e) as [[e' fe] ok]. apply H. Qed.

End Fv.

Definition choose_masks (e : exp) : WM.t (list bool) :=
  let cands := match fixpoint.live_masks e with Some L => [L] | None => [] end in
  match find (fun L => snd (dpe_fv L e)) cands with
  | Some L => L
  | None => WM.empty _
  end.

Lemma choose_masks_ok e : all_funs (mask_ok (choose_masks e)) e.
Proof.
  unfold choose_masks.
  destruct (find (fun L => snd (dpe_fv L e)) _) eqn:Hf.
  - eapply find_some in Hf. eapply (proj1 (mchk_spec _)). rewrite <- dpe_fv_ok. apply Hf.
  - assert (Hm : forall w xs e', (fun _ _ _ => True) w xs e' -> mask_ok (WM.empty _) w xs e').
    { intros w xs e' _ bs _ HL. rewrite WM.gempty in HL. discriminate. }
    exact (proj1 (all_funs_mono _ _ Hm) e (proj1 all_funs_true e)).
Qed.

Definition dpe_top (e : exp) : exp := fst (fst (dpe_fv (choose_masks e) e)).

(** * Correctness of the implementation *)

Theorem dpe_top_trans e : trans (choose_masks e) (esize e) (esize e) e (dpe_top e).
Proof. unfold dpe_top. rewrite dpe_fv_fst. eapply dpe_trans; [ eapply choose_masks_ok | lia ]. Qed.

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
