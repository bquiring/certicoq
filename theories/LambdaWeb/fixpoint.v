(* A constraint solver, and the flow analyses of the λweb passes built on it.

   * The solver

   A problem is a list of constraints [k ⊒ t] over a join semi-lattice
   [(A, bot, join)], where [k] is a key and [t] is a constant or the value
   of a key.  The solver computes the least solution by round-robin
   iteration: it applies every constraint in turn ([round]), and repeats
   until a round changes nothing.

   Correctness ([solve_correct]): if [eqb] decides equality, [join] is a
   join semi-lattice with least element [bot], and its height is at most
   [h], then [solve h cs] returns [Some s], and [s] is the least map
   satisfying every constraint of [cs].  A round that changes the map
   raises the value of the target of a constraint, which can happen at most
   [h] times per target, so at most [h * length cs] rounds change the map,
   and the fuel suffices.  The passes do not rely on this theorem, as they
   check the results of their analyses, but it shows the analyses never
   fail and compute least solutions.

   * The analyses

   The keys are the variables of a program and the parameter positions of
   its webs.  Each analysis generates one constraint per flow:

   - Liveness (for dead parameter elimination), over booleans: a variable is
     live if a case analyzes it, a primitive or [halt] uses it, a call calls
     it, or it flows into a live variable or parameter position; a parameter
     position is live if the parameter of some function of the web is.  A
     parameter that is only passed on to the same position of a recursive
     call stays dead.
   - Known constructors (for arity raising and constant propagation), over
     the flat lattice of constructor shapes: a variable bound by [Econstr]
     holds that constructor, a parameter holds what its position receives,
     and a position receives the arguments of all calls of the web.

   Webs whose functions disagree on their arity, or have repeated
   parameters, and exposed webs, are not transformed: their positions are
   live and unknown. *)

From Stdlib Require Import NArith.BinNat Lists.List Bool.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaWeb Require Import syntax.

Import ListNotations.

(** * The solver *)

Section Solver.

  Context {A : Type} (bot : A) (join : A -> A -> A) (eqb : A -> A -> bool).

  Inductive term : Type :=
  | Const (a : A)
  | Look (k : positive).

  (** [(k, t)]: the value of [k] is at least [t] *)
  Definition constr : Type := positive * term.

  Definition get (s : M.t A) (k : positive) : A :=
    match s ! k with Some a => a | None => bot end.

  Definition eval (s : M.t A) (t : term) : A :=
    match t with Const a => a | Look k => get s k end.

  (** Apply a constraint; the flag records a change *)
  Definition update (sc : M.t A * bool) (c : constr) : M.t A * bool :=
    let '(s, ch) := sc in
    let '(k, t) := c in
    let old := get s k in
    let nw := join old (eval s t) in
    if eqb nw old then (s, ch) else (M.set k nw s, true).

  Definition round (cs : list constr) (s : M.t A) : M.t A * bool :=
    fold_left update cs (s, false).

  Fixpoint iterate (fuel : nat) (cs : list constr) (s : M.t A) : option (M.t A) :=
    match fuel with
    | O => None
    | S fuel =>
        let '(s', ch) := round cs s in
        if ch then iterate fuel cs s' else Some s'
    end.

  (** [h]: the height of the lattice *)
  Definition solve (h : nat) (cs : list constr) : option (M.t A) :=
    iterate (S (h * length cs)) cs (M.empty A).

End Solver.

Arguments term : clear implicits.
Arguments constr : clear implicits.

(** ** Correctness of the solver

    The lattice is given by its join, with least element [bot], and its
    height by a rank function: ranks are at most [h], and a strictly larger
    element has a strictly larger rank.  The order is [le a b := join a b = b]. *)

Section SolverCorrect.

  Local Open Scope nat_scope.

  Context {A : Type} (bot : A) (join : A -> A -> A) (eqb : A -> A -> bool)
          (rank : A -> nat) (h : nat).

  Hypothesis eqb_spec : forall a b, eqb a b = true <-> a = b.
  Hypothesis join_comm : forall a b, join a b = join b a.
  Hypothesis join_assoc : forall a b c, join (join a b) c = join a (join b c).
  Hypothesis join_idem : forall a, join a a = a.
  Hypothesis join_bot : forall a, join bot a = a.

  Definition le (a b : A) : Prop := join a b = b.

  Hypothesis rank_bound : forall a, rank a <= h.
  Hypothesis rank_lt : forall a b, le a b -> a <> b -> rank a < rank b.

  (** A map satisfies a constraint, a set of constraints; one map is below
      another *)
  Definition sat (s : M.t A) (c : constr A) : Prop := le (eval bot s (snd c)) (get bot s (fst c)).

  Definition solution (cs : list (constr A)) (s : M.t A) : Prop := forall c, In c cs -> sat s c.

  Definition below (s s' : M.t A) : Prop := forall k, le (get bot s k) (get bot s' k).

  Lemma le_refl a : le a a.
  Proof. apply join_idem. Qed.

  Lemma le_trans a b c : le a b -> le b c -> le a c.
  Proof. unfold le. intros H1 H2. rewrite <- H2, <- join_assoc, H1. reflexivity. Qed.

  Lemma le_join_l a b : le a (join a b).
  Proof. unfold le. rewrite <- join_assoc, join_idem. reflexivity. Qed.

  Lemma le_join_r a b : le b (join a b).
  Proof. rewrite join_comm. apply le_join_l. Qed.

  Lemma join_lub a b c : le a c -> le b c -> le (join a b) c.
  Proof. unfold le. intros H1 H2. rewrite join_assoc, H2, H1. reflexivity. Qed.

  Lemma le_bot a : le bot a.
  Proof. apply join_bot. Qed.

  Lemma rank_mono a b : le a b -> rank a <= rank b.
  Proof.
    intros H. destruct (eqb a b) eqn:E.
    - apply eqb_spec in E. subst. lia.
    - assert (a <> b) by (intros ->; rewrite (proj2 (eqb_spec b b) eq_refl) in E; discriminate).
      pose proof (rank_lt a b H H0). lia.
  Qed.

  Lemma below_refl s : below s s.
  Proof. intros k. apply le_refl. Qed.

  Lemma below_trans s1 s2 s3 : below s1 s2 -> below s2 s3 -> below s1 s3.
  Proof. intros H1 H2 k. eapply le_trans; eauto. Qed.

  Lemma eval_mono s s' t : below s s' -> le (eval bot s t) (eval bot s' t).
  Proof. intros H. destruct t; simpl. apply le_refl. apply H. Qed.

  Lemma get_set s k k' a : get bot (M.set k a s) k' = if Pos.eq_dec k' k then a else get bot s k'.
  Proof. unfold get. rewrite M.gsspec. destruct (peq k' k); destruct (Pos.eq_dec k' k); congruence. Qed.

  (** An update only raises the map *)
  Lemma update_grow s ch c : below s (fst (update bot join eqb (s, ch) c)).
  Proof.
    destruct c as [k t]. unfold update. destruct eqb; simpl. apply below_refl.
    intros k'. rewrite get_set. destruct Pos.eq_dec; subst. apply le_join_l. apply le_refl.
  Qed.

  (** An update stays below every solution *)
  Lemma update_below cs s ch c σ :
    solution cs σ -> In c cs -> below s σ -> below (fst (update bot join eqb (s, ch) c)) σ.
  Proof.
    intros Hσ Hc Hs. destruct c as [k t]. unfold update. destruct eqb; simpl. auto.
    intros k'. rewrite get_set. destruct Pos.eq_dec; subst; auto.
    apply join_lub. auto. eapply le_trans. apply eval_mono; eauto. apply (Hσ _ Hc).
  Qed.

  Lemma fold_below cs cs0 s ch σ :
    solution cs σ -> incl cs0 cs -> below s σ ->
    below (fst (fold_left (update bot join eqb) cs0 (s, ch))) σ.
  Proof.
    intros Hσ. revert s ch. induction cs0 as [|c cs0 IH]; intros s ch Hi Hs; cbn [fold_left]. auto.
    destruct (update bot join eqb (s, ch) c) as [s1 ch1] eqn:E.
    apply IH. eapply incl_cons_inv; eauto.
    replace s1 with (fst (update bot join eqb (s, ch) c)) by (rewrite E; reflexivity).
    eapply update_below; eauto. apply Hi. left. reflexivity.
  Qed.

  Lemma update_eq s ch k t :
    update bot join eqb (s, ch) (k, t) =
    if eqb (join (get bot s k) (eval bot s t)) (get bot s k) then (s, ch)
    else (M.set k (join (get bot s k) (eval bot s t)) s, true).
  Proof. reflexivity. Qed.

  Lemma fold_true cs s : snd (fold_left (update bot join eqb) cs (s, true)) = true.
  Proof.
    revert s. induction cs as [|[k t] cs IH]; intros s; simpl. reflexivity.
    destruct eqb; apply IH.
  Qed.

  (** A round that changes nothing ends at a solution *)
  Lemma fold_false cs0 s ch s' :
    fold_left (update bot join eqb) cs0 (s, ch) = (s', false) ->
    s' = s /\ ch = false /\ solution cs0 s.
  Proof.
    revert s ch. induction cs0 as [|[k t] cs0 IH]; intros s ch H; cbn [fold_left] in H; rewrite ?update_eq in H.
    - inv H. split; [|split]; auto. intros c [].
    - destruct (eqb (join (get bot s k) (eval bot s t)) (get bot s k)) eqn:E.
      + apply IH in H. destruct H as (-> & -> & Hs). split; [|split]; auto.
        intros c [<- | Hc]; auto. apply eqb_spec in E. unfold sat, le; simpl.
        rewrite join_comm. exact E.
      + assert (Ht : snd (s', false) = true) by (rewrite <- H; apply fold_true).
        discriminate.
  Qed.

  (** The potential of a map: the sum of the ranks of the targets *)
  Fixpoint pot (s : M.t A) (ks : list positive) : nat :=
    match ks with
    | [] => 0
    | k :: ks => rank (get bot s k) + pot s ks
    end.

  Lemma pot_bound s ks : pot s ks <= h * length ks.
  Proof. induction ks; simpl. lia. pose proof (rank_bound (get bot s a)). lia. Qed.

  Lemma pot_mono s s' ks : below s s' -> pot s ks <= pot s' ks.
  Proof. intros H. induction ks; simpl. lia. specialize (rank_mono _ _ (H a)). lia. Qed.

  Lemma pot_lt s s' ks k :
    below s s' -> In k ks -> rank (get bot s k) < rank (get bot s' k) -> pot s ks < pot s' ks.
  Proof.
    intros H. induction ks as [|k' ks IH]; intros Hk Hr; simpl. destruct Hk.
    destruct Hk as [<- | Hk].
    - specialize (pot_mono _ _ ks H). lia.
    - specialize (IH Hk Hr). specialize (rank_mono _ _ (H k')). lia.
  Qed.

  (** A round that changes the map raises the rank of a target *)
  Lemma fold_change cs0 s ch s' ch' :
    fold_left (update bot join eqb) cs0 (s, ch) = (s', ch') ->
    below s s' /\
    (ch' = true -> ch = true \/ exists k, In k (map fst cs0) /\ rank (get bot s k) < rank (get bot s' k)).
  Proof.
    revert s ch. induction cs0 as [|[k t] cs0 IH]; intros s ch H; cbn [fold_left] in H; rewrite ?update_eq in H.
    - inv H. split. apply below_refl. auto.
    - destruct (eqb (join (get bot s k) (eval bot s t)) (get bot s k)) eqn:E.
      + apply IH in H. destruct H as [Hb Hc]. split; auto.
        intros Hch. destruct (Hc Hch) as [? | (k' & Hk' & Hr)]; auto.
        right. exists k'. split; auto. right. auto.
      + change (fold_left (update bot join eqb) cs0 (M.set k (join (get bot s k) (eval bot s t)) s, true) = (s', ch')) in H.
        set (s1 := M.set k (join (get bot s k) (eval bot s t)) s) in H.
        assert (Hs1 : below s s1).
        { replace s1 with (fst (update bot join eqb (s, ch) (k, t))) by (simpl; rewrite E; reflexivity).
          apply update_grow. }
        apply IH in H. destruct H as [Hb _]. split. eapply below_trans; eauto.
        intros _. right. exists k. split. left. reflexivity.
        assert (Hne : get bot s k <> join (get bot s k) (eval bot s t)).
        { intros Heq. rewrite <- Heq in E. rewrite (proj2 (eqb_spec _ _) eq_refl) in E. discriminate. }
        pose proof (rank_lt _ _ (le_join_l (get bot s k) (eval bot s t)) Hne).
        specialize (rank_mono _ _ (Hb k)). unfold s1. rewrite get_set.
        destruct Pos.eq_dec; [|congruence]. lia.
  Qed.

  Lemma iterate_correct cs fuel s :
    h * length cs < pot s (map fst cs) + fuel ->
    (forall σ, solution cs σ -> below s σ) ->
    exists s', iterate bot join eqb fuel cs s = Some s' /\ solution cs s' /\
               forall σ, solution cs σ -> below s' σ.
  Proof.
    revert s. induction fuel as [|fuel IH]; intros s Hf Hs; simpl.
    - specialize (pot_bound s (map fst cs)). rewrite length_map. lia.
    - unfold round. destruct (fold_left (update bot join eqb) cs (s, false)) as [s' ch] eqn:E.
      destruct ch.
      + apply IH.
        * apply fold_change in E. destruct E as [Hb Hc].
          destruct (Hc eq_refl) as [? | (k & Hk & Hr)]; [discriminate|].
          specialize (pot_lt _ _ _ _ Hb Hk Hr). lia.
        * intros σ Hσ. replace s' with (fst (fold_left (update bot join eqb) cs (s, false))) by (rewrite E; reflexivity).
          apply fold_below with cs; auto. apply incl_refl.
      + apply fold_false in E. destruct E as (-> & _ & Hsol). eauto.
  Qed.

  (** The solver returns the least solution *)
  Theorem solve_correct cs :
    exists s, solve bot join eqb h cs = Some s /\ solution cs s /\
              forall σ, solution cs σ -> below s σ.
  Proof.
    apply iterate_correct. unfold solve. eapply Nat.lt_le_trans; [apply Nat.lt_succ_diag_r | apply Nat.le_add_l]. intros σ _ k. unfold get at 1. rewrite M.gempty. apply le_bot.
  Qed.

End SolverCorrect.

(** * Lattices *)

(** Constructor shapes: none yet, a constructor of web [w] with tag [c] and
    [n] fields, or several *)
Inductive cval : Type :=
| CBot
| CCon (w : web) (c : ctor_tag) (n : nat)
| CTop.

Definition cval_eqb (a b : cval) : bool :=
  match a, b with
  | CBot, CBot | CTop, CTop => true
  | CCon w c n, CCon w' c' n' => web_eqb w w' && Pos.eqb c c' && Nat.eqb n n'
  | _, _ => false
  end.

Definition cval_join (a b : cval) : cval :=
  match a, b with
  | CBot, b => b
  | a, CBot => a
  | CCon _ _ _, CCon _ _ _ => if cval_eqb a b then a else CTop
  | _, _ => CTop
  end.

(** The two lattices satisfy the solver's hypotheses: booleans have height
    1, constructor shapes height 2. *)

Local Open Scope nat_scope.

Definition bool_rank (b : bool) : nat := if b then 1 else 0.

Theorem solve_bool cs :
  exists s, solve false orb Bool.eqb 1 cs = Some s /\ solution false orb cs s /\
            forall σ, solution false orb cs σ -> below false orb s σ.
Proof.
  apply solve_correct with (rank := bool_rank).
  - intros. apply Bool.eqb_true_iff.
  - apply orb_comm.
  - intros. symmetry. apply orb_assoc.
  - apply orb_diag.
  - reflexivity.
  - intros []; simpl; lia.
  - unfold le. intros [] []; simpl; congruence || lia.
Qed.

Definition cval_rank (a : cval) : nat := match a with CBot => 0 | CCon _ _ _ => 1 | CTop => 2 end.

Lemma cval_eqb_spec a b : cval_eqb a b = true <-> a = b.
Proof.
  destruct a, b; simpl; split; intros H; try congruence.
  - repeat rewrite andb_true_iff in H. destruct H as [[H1 H2] H3].
    apply web_eqb_eq in H1. apply Pos.eqb_eq in H2. apply Nat.eqb_eq in H3. subst. reflexivity.
  - inv H. rewrite web_eqb_refl, Pos.eqb_refl, Nat.eqb_refl. reflexivity.
Qed.

Lemma cval_join_comm a b : cval_join a b = cval_join b a.
Proof.
  destruct a as [|w c n|], b as [|w' c' n'|]; simpl; try reflexivity.
  destruct (web_eqb w w') eqn:E1, (web_eqb w' w) eqn:E1';
    try (apply web_eqb_eq in E1 || apply web_eqb_eq in E1'; subst; rewrite web_eqb_refl in *; discriminate);
    simpl; try reflexivity.
  apply web_eqb_eq in E1. subst.
  destruct (Pos.eqb c c') eqn:E2, (Pos.eqb c' c) eqn:E2';
    try (apply Pos.eqb_eq in E2 || apply Pos.eqb_eq in E2'; subst; rewrite Pos.eqb_refl in *; discriminate);
    simpl; try reflexivity.
  apply Pos.eqb_eq in E2. subst.
  destruct (Nat.eqb n n') eqn:E3, (Nat.eqb n' n) eqn:E3';
    try (apply Nat.eqb_eq in E3 || apply Nat.eqb_eq in E3'; subst; rewrite Nat.eqb_refl in *; discriminate);
    try reflexivity.
  apply Nat.eqb_eq in E3. subst. reflexivity.
Qed.

Lemma cval_join_idem a : cval_join a a = a.
Proof. destruct a; cbn [cval_join]; auto. rewrite (proj2 (cval_eqb_spec _ _) eq_refl). reflexivity. Qed.

Lemma cval_join_assoc a b c : cval_join (cval_join a b) c = cval_join a (cval_join b c).
Proof.
  destruct a as [|w c1 n1|], b as [|w2 c2 n2|], c as [|w3 c3 n3|]; cbn [cval_join]; try reflexivity;
    repeat match goal with
           | |- context [cval_eqb ?x ?y] => let E := fresh "E" in destruct (cval_eqb x y) eqn:E; cbn [cval_join]
           | H : cval_eqb _ _ = true |- _ => apply cval_eqb_spec in H; inv H
           end; try reflexivity; try congruence;
    repeat match goal with
           | H : cval_eqb ?x ?x = false |- _ => rewrite (proj2 (cval_eqb_spec x x) eq_refl) in H; discriminate
           end.
Qed.

Theorem solve_cval cs :
  exists s, solve CBot cval_join cval_eqb 2 cs = Some s /\ solution CBot cval_join cs s /\
            forall σ, solution CBot cval_join cs σ -> below CBot cval_join s σ.
Proof.
  apply solve_correct with (rank := cval_rank).
  - apply cval_eqb_spec.
  - apply cval_join_comm.
  - apply cval_join_assoc.
  - apply cval_join_idem.
  - reflexivity.
  - intros []; simpl; lia.
  - unfold le. intros [|w c n|] [|w' c' n'|]; cbn [cval_join cval_rank]; intros H Hne; try congruence; try lia.
    destruct (cval_eqb (CCon w c n) (CCon w' c' n')) eqn:E; [apply cval_eqb_spec in E|]; congruence.
Qed.

(** * Keys *)

Fixpoint shiftz (n : nat) (t : positive) : positive :=
  match n with
  | O => t
  | S n => xO (shiftz n t)
  end.

(** [emb p k]: the bits of [p], each preceded by a zero, then a one, then
    [k]; injective in [p] and [k] *)
Fixpoint emb (p k : positive) : positive :=
  match p with
  | xO p => xO (xO (emb p k))
  | xI p => xO (xI (emb p k))
  | xH => xI k
  end.

Definition wcode (w : web) : positive := match w with Internal p => xO p | Exposed t => xI t end.

Definition kvar (x : var) : positive := xO x.

(** The [i]-th parameter position of web [w] *)
Definition kparam (w : web) (i : nat) : positive := xI (xI (emb (wcode w) (Pos.of_succ_nat i))).

(** The [i]-th field of the constructors of web [w] with tag [t] *)
Definition kfield (w : web) (t : ctor_tag) (i : nat) : positive :=
  xI (xO (emb (wcode w) (emb t (Pos.of_succ_nat i)))).

Definition imap {B C} (f : nat -> B -> C) (l : list B) : list C :=
  map (fun p => f (fst p) (snd p)) (combine (seq 0 (length l)) l).

(** * The webs that are transformed *)

Fixpoint nodupb (xs : list var) : bool :=
  match xs with
  | [] => true
  | x :: xs => negb (existsb (Pos.eqb x) xs) && nodupb xs
  end.

(** The arity of the functions of each web, [None] if they disagree or
    have repeated parameters *)
Definition add_arity (w : web) (xs : list var) (tbl : WM.t (option nat)) : WM.t (option nat) :=
  if nodupb xs then
    match WM.get w tbl with
    | None => WM.set w (Some (length xs)) tbl
    | Some None => tbl
    | Some (Some n) => if Nat.eqb n (length xs) then tbl else WM.set w None tbl
    end
  else WM.set w None tbl.

Fixpoint arities (e : exp) (tbl : WM.t (option nat)) : WM.t (option nat) :=
  match e with
  | Econstr _ _ _ _ k | Eproj _ _ _ _ _ k | Eletapp _ _ _ _ k
  | Eprim_val _ _ k | Eprim _ _ _ k => arities k tbl
  | Ecase _ _ cl =>
      (fix go (cl : list (ctor_tag * exp)) tbl :=
         match cl with
         | [] => tbl
         | (_, e) :: cl => go cl (arities e tbl)
         end) cl tbl
  | Efun B k => arities k (arities_fd B tbl)
  | Eapp _ _ _ | Ehalt _ => tbl
  end
with arities_fd (B : fundefs) (tbl : WM.t (option nat)) : WM.t (option nat) :=
  match B with
  | Fcons _ w xs e B => arities_fd B (arities e (add_arity w xs tbl))
  | Fnil => tbl
  end.

Section Analyses.

  Variable (ar : WM.t (option nat)).

  (** The webs whose positions are tracked *)
  Definition okw (w : web) : bool :=
    negb (exposedb w) && match WM.get w ar with Some (Some _) => true | _ => false end.

  (** ** Liveness *)

  Definition live_call (f : var) (w : web) (ys : list var) : list (constr bool) :=
    (kvar f, Const true) ::
    (if okw w then imap (fun i y => (kvar y, Look (kparam w i))) ys
     else map (fun y => (kvar y, Const true)) ys).

  Fixpoint live_cs (e : exp) (acc : list (constr bool)) : list (constr bool) :=
    match e with
    | Econstr x _ _ ys k => live_cs k (map (fun y => (kvar y, Look (kvar x))) ys ++ acc)
    | Eproj x _ _ _ y k => live_cs k ((kvar y, Look (kvar x)) :: acc)
    | Ecase x _ cl =>
        (fix go (cl : list (ctor_tag * exp)) acc :=
           match cl with
           | [] => acc
           | (_, e) :: cl => go cl (live_cs e acc)
           end) cl ((kvar x, Const true) :: acc)
    | Eletapp _ f w ys k => live_cs k (live_call f w ys ++ acc)
    | Efun B k => live_cs k (live_cs_fd B acc)
    | Eapp f w ys => live_call f w ys ++ acc
    | Eprim_val _ _ k => live_cs k acc
    | Eprim _ _ ys k => live_cs k (map (fun y => (kvar y, Const true)) ys ++ acc)
    | Ehalt x => (kvar x, Const true) :: acc
    end
  with live_cs_fd (B : fundefs) (acc : list (constr bool)) : list (constr bool) :=
    match B with
    | Fcons _ w xs e B =>
        let ps := if okw w then imap (fun i x => (kparam w i, Look (kvar x))) xs
                  else imap (fun i _ => (kparam w i, Const true)) xs in
        live_cs_fd B (live_cs e (ps ++ acc))
    | Fnil => acc
    end.

  (** ** Known constructors

      With [fld], the fields of constructors are tracked: a projection
      receives what the constructors of its web and tag store at that
      field; otherwise it is unknown. *)

  Variable (fld : bool).

  Definition con_call (w : web) (ys : list var) : list (constr cval) :=
    if okw w then imap (fun i y => (kparam w i, Look (kvar y))) ys else [].

  Fixpoint con_cs (e : exp) (acc : list (constr cval)) : list (constr cval) :=
    match e with
    | Econstr x w c ys k =>
        let fs := if fld then imap (fun i y => (kfield w c i, Look (kvar y))) ys else [] in
        con_cs k ((kvar x, Const (CCon w c (length ys))) :: fs ++ acc)
    | Eproj x w c n _ k =>
        con_cs k ((kvar x, if fld then Look (kfield w c (N.to_nat n)) else Const CTop) :: acc)
    | Eprim_val x _ k | Eprim x _ _ k => con_cs k ((kvar x, Const CTop) :: acc)
    | Ecase _ _ cl =>
        (fix go (cl : list (ctor_tag * exp)) acc :=
           match cl with
           | [] => acc
           | (_, e) :: cl => go cl (con_cs e acc)
           end) cl acc
    | Eletapp x _ w ys k => con_cs k ((kvar x, Const CTop) :: con_call w ys ++ acc)
    | Efun B k => con_cs k (con_cs_fd B acc)
    | Eapp _ w ys => con_call w ys ++ acc
    | Ehalt _ => acc
    end
  with con_cs_fd (B : fundefs) (acc : list (constr cval)) : list (constr cval) :=
    match B with
    | Fcons f w xs e B =>
        let ps := if okw w then imap (fun i x => (kvar x, Look (kparam w i))) xs
                  else map (fun x => (kvar x, Const CTop)) xs in
        con_cs_fd B (con_cs e ((kvar f, Const CTop) :: ps ++ acc))
    | Fnil => acc
    end.

End Analyses.

(** * Results *)

(** The tracked webs and their arities *)
Definition tracked (e : exp) : list (web * nat) :=
  let ar := arities e (WM.empty _) in
  flat_map (fun '(w, o) => match o with
                           | Some n => if okw ar w then [(w, n)] else []
                           | None => []
                           end) (WM_elements ar).

(** For every tracked web, which parameters are live *)
Definition live_masks (e : exp) : option (WM.t (list bool)) :=
  let ar := arities e (WM.empty _) in
  match solve false orb Bool.eqb 1 (live_cs ar e []) with
  | Some s =>
      Some (fold_left (fun L '(w, n) => WM.set w (map (fun i => get false s (kparam w i)) (seq 0 n)) L)
                      (tracked e) (WM.empty _))
  | None => None
  end.

(** For every tracked web, the constructor shape each parameter receives.
    A position that receives nothing (its web is never called) is unknown:
    its parameters may still be passed on, and a transformation needs a
    shape for them.  Marking these positions unknown only raises values, so
    a second solution has no such positions left. *)
Definition con_solve (fld : bool) (e : exp) : option (M.t cval) :=
  let ar := arities e (WM.empty _) in
  let cs := con_cs ar fld e [] in
  let tr := tracked e in
  match solve CBot cval_join cval_eqb 2 cs with
  | Some s =>
      let never := flat_map (fun '(w, n) => flat_map (fun i => match get CBot s (kparam w i) with
                                                               | CBot => [(kparam w i, Const CTop)]
                                                               | _ => []
                                                               end) (seq 0 n)) tr in
      solve CBot cval_join cval_eqb 2 (never ++ cs)
  | None => None
  end.

Definition param_cons (e : exp) : option (WM.t (list cval)) :=
  match con_solve false e with
  | Some s =>
      Some (fold_left (fun L '(w, n) => WM.set w (map (fun i => get CBot s (kparam w i)) (seq 0 n)) L)
                      (tracked e) (WM.empty _))
  | None => None
  end.

(** ** Known variables

    Given the shapes [shp] of a solution of the known-constructor analysis
    with fields, a variable is unknown (true) unless it is bound by a
    constructor whose fields of known shape hold variables that are known
    and of that shape, by a projection of a field of known shape of a known
    variable, or as a parameter at a position that only receives known
    variables.  Arity raising's environment of known variables follows the
    same rules, with the field table [fshape]. *)

Section Known.

  Variables (ar : WM.t (option nat)) (shp : positive -> cval).

  Definition cshape (v : cval) : option (web * nat * ctor_tag) :=
    match v with CCon wc c n => Some (wc, n, c) | _ => None end.

  Definition fshape (w : web) (t : ctor_tag) (i : nat) : option (web * nat * ctor_tag) :=
    cshape (shp (kfield w t i)).

  Definition same_shape (a b : option (web * nat * ctor_tag)) : bool :=
    match a, b with
    | Some (w, n, c), Some (w', n', c') => web_eqb w w' && Nat.eqb n n' && Pos.eqb c c'
    | _, _ => false
    end.

  Definition unk_constr (x : var) (w : web) (t : ctor_tag) (ys : list var) : list (constr bool) :=
    concat (imap (fun i y => match fshape w t i with
                             | Some s => if same_shape (cshape (shp (kvar y))) (Some s)
                                         then [(kvar x, Look (kvar y))] else [(kvar x, Const true)]
                             | None => []
                             end) ys).

  Definition unk_call (w : web) (ys : list var) : list (constr bool) :=
    if okw ar w then imap (fun i y => (kparam w i, Look (kvar y))) ys else [].

  Fixpoint unk_cs (e : exp) (acc : list (constr bool)) : list (constr bool) :=
    match e with
    | Econstr x w t ys k => unk_cs k (unk_constr x w t ys ++ acc)
    | Eproj x w t n y k =>
        let c := match fshape w t (N.to_nat n) with Some _ => Look (kvar y) | None => Const true end in
        unk_cs k ((kvar x, c) :: acc)
    | Ecase _ _ cl =>
        (fix go (cl : list (ctor_tag * exp)) acc :=
           match cl with
           | [] => acc
           | (_, e) :: cl => go cl (unk_cs e acc)
           end) cl acc
    | Eletapp x _ w ys k => unk_cs k ((kvar x, Const true) :: unk_call w ys ++ acc)
    | Efun B k => unk_cs k (unk_cs_fd B acc)
    | Eapp _ w ys => unk_call w ys ++ acc
    | Eprim_val x _ k | Eprim x _ _ k => unk_cs k ((kvar x, Const true) :: acc)
    | Ehalt _ => acc
    end
  with unk_cs_fd (B : fundefs) (acc : list (constr bool)) : list (constr bool) :=
    match B with
    | Fcons f w xs e B =>
        let ps := if okw ar w then imap (fun i x => (kvar x, Look (kparam w i))) xs
                  else map (fun x => (kvar x, Const true)) xs in
        unk_cs_fd B (unk_cs e ((kvar f, Const true) :: ps ++ acc))
    | Fnil => acc
    end.

End Known.

(** The results of the analyses with fields, for arity raising: the shapes,
    and for every tracked web, the shape and whether it is unknown of each
    position *)
Definition field_analysis (e : exp) :
  option ((positive -> cval) * WM.t (list (cval * bool))) :=
  let ar := arities e (WM.empty _) in
  match con_solve true e with
  | Some s =>
      let shp := get CBot s in
      match solve false orb Bool.eqb 1 (unk_cs ar shp e []) with
      | Some u =>
          Some (shp, fold_left (fun L '(w, n) =>
                                  WM.set w (map (fun i => (shp (kparam w i), get false u (kparam w i))) (seq 0 n)) L)
                               (tracked e) (WM.empty _))
      | None => None
      end
  | None => None
  end.

(** ** Records that are only projected

    Arity raising rebuilds a flattened record on function entry, which
    allocates unless every use of the record is a projection or a case
    analysis, which the λANF shrinker resolves once the record is known.  A
    variable escapes (true) if it is used otherwise: stored in a
    constructor, used by a primitive or [halt], or passed at a position that
    is not flattened.  Passing it at a flattened position
    projects its fields, so it escapes only if that position does.  A
    position escapes if a parameter at that position does.  [flat w i]: the
    positions that may be flattened. *)

Section Escape.

  Variables (ar : WM.t (option nat)) (flat : web -> nat -> bool).

  Definition esc_call (f : var) (w : web) (ys : list var) : list (constr bool) :=
    (kvar f, Const true) ::
    imap (fun i y => if okw ar w && flat w i then (kvar y, Look (kparam w i)) else (kvar y, Const true)) ys.

  Fixpoint esc_cs (e : exp) (acc : list (constr bool)) : list (constr bool) :=
    match e with
    | Econstr _ _ _ ys k => esc_cs k (map (fun y => (kvar y, Const true)) ys ++ acc)
    | Eproj _ _ _ _ _ k | Eprim_val _ _ k => esc_cs k acc
    | Ecase _ _ cl =>
        (fix go (cl : list (ctor_tag * exp)) acc :=
           match cl with
           | [] => acc
           | (_, e) :: cl => go cl (esc_cs e acc)
           end) cl acc
    | Eletapp _ f w ys k => esc_cs k (esc_call f w ys ++ acc)
    | Efun B k => esc_cs k (esc_cs_fd B acc)
    | Eapp f w ys => esc_call f w ys ++ acc
    | Eprim _ _ ys k => esc_cs k (map (fun y => (kvar y, Const true)) ys ++ acc)
    | Ehalt x => (kvar x, Const true) :: acc
    end
  with esc_cs_fd (B : fundefs) (acc : list (constr bool)) : list (constr bool) :=
    match B with
    | Fcons _ w xs e B =>
        let ps := if okw ar w then imap (fun i x => (kparam w i, Look (kvar x))) xs else [] in
        esc_cs_fd B (esc_cs e (ps ++ acc))
    | Fnil => acc
    end.

End Escape.

(** For every tracked web, which positions escape *)
Definition escaping (e : exp) (flat : web -> nat -> bool) : option (WM.t (list bool)) :=
  let ar := arities e (WM.empty _) in
  match solve false orb Bool.eqb 1 (esc_cs ar flat e []) with
  | Some s =>
      Some (fold_left (fun L '(w, n) => WM.set w (map (fun i => get false s (kparam w i)) (seq 0 n)) L)
                      (tracked e) (WM.empty _))
  | None => None
  end.

(** * Diagnostics *)

(** The uses of variables that make them escape, as (variable, reason):
    1 stored in a constructor, 2 used by a primitive, 3 returned by [halt],
    5 passed to a web that is not tracked, 6 called, and, passed at a
    position of a tracked web, [cls w i] (the kind of that position). *)
Section Why.

  Variables (ar : WM.t (option nat)) (cls : web -> nat -> nat).

  Definition why_call (f : var) (w : web) (ys : list var) : list (var * nat) :=
    (f, 6%nat) :: imap (fun i y => (y, if okw ar w then cls w i else 5%nat)) ys.

  Fixpoint why (e : exp) (acc : list (var * nat)) : list (var * nat) :=
    match e with
    | Econstr _ _ _ ys k => why k (map (fun y => (y, 1%nat)) ys ++ acc)
    | Eproj _ _ _ _ _ k | Eprim_val _ _ k => why k acc
    | Ecase _ _ cl =>
        (fix go (cl : list (ctor_tag * exp)) acc :=
           match cl with
           | [] => acc
           | (_, e) :: cl => go cl (why e acc)
           end) cl acc
    | Eletapp _ f w ys k => why k (why_call f w ys ++ acc)
    | Efun B k => why k (why_fd B acc)
    | Eapp f w ys => why_call f w ys ++ acc
    | Eprim _ _ ys k => why k (map (fun y => (y, 2%nat)) ys ++ acc)
    | Ehalt x => (x, 3%nat) :: acc
    end
  with why_fd (B : fundefs) (acc : list (var * nat)) : list (var * nat) :=
    match B with
    | Fcons _ _ _ e B => why_fd B (why e acc)
    | Fnil => acc
    end.

End Why.

(** The parameters of the program, with their positions *)
Fixpoint param_pos (e : exp) (acc : list (var * (web * nat))) : list (var * (web * nat)) :=
  match e with
  | Econstr _ _ _ _ k | Eproj _ _ _ _ _ k | Eprim_val _ _ k | Eprim _ _ _ k | Eletapp _ _ _ _ k => param_pos k acc
  | Ecase _ _ cl =>
      (fix go (cl : list (ctor_tag * exp)) acc :=
         match cl with
         | [] => acc
         | (_, e) :: cl => go cl (param_pos e acc)
         end) cl acc
  | Efun B k => param_pos k (param_pos_fd B acc)
  | Eapp _ _ _ | Ehalt _ => acc
  end
with param_pos_fd (B : fundefs) (acc : list (var * (web * nat))) : list (var * (web * nat)) :=
  match B with
  | Fcons _ w xs e B => param_pos_fd B (param_pos e (imap (fun i x => (x, (w, i))) xs ++ acc))
  | Fnil => acc
  end.

(** For the parameters at the positions [sel], how often each reason
    (1 to [n]) occurs among their uses *)
Definition why_hist (e : exp) (cls : web -> nat -> nat) (sel : web -> nat -> bool) (n : nat) : list nat :=
  let ar := arities e (WM.empty _) in
  let ps := List.filter (fun p : var * (web * nat) => sel (fst (snd p)) (snd (snd p))) (param_pos e []) in
  let xs := fold_left (fun m (p : var * (web * nat)) => M.set (fst p) tt m) ps (M.empty unit) in
  let ws := List.filter (fun p : var * nat => match xs ! (fst p) with Some _ => true | None => false end) (why ar cls e []) in
  map (fun r => length (List.filter (fun p : var * nat => Nat.eqb r (snd p)) ws)) (seq 1 n).
