(* Correctness of [freshen]: the freshened program is α-equivalent to the
   source, binds every name once, and draws its bound names from the fresh
   pool, so it is well scoped and the pool stays fresh for it.

   Unique bindings need the functions of a bundle to have distinct names:
   [freshen] renames a name the same way wherever it occurs, so two
   functions of one bundle with the same name stay equal. *)

Require Import Common.compM.
Require Import LambdaANF.term LambdaANF.term_util LambdaANF.set_util LambdaANF.identifiers
        LambdaANF.Ensembles_util LambdaANF.List_util LambdaANF.functions LambdaANF.tactics
        LambdaANF.map_util LambdaANF.alpha_conv LambdaANF.state LambdaANF.freshen.
Require Import compcert.lib.Coqlib.
From Stdlib Require Import Lists.List NArith.BinNat PArith.BinPos Sets.Ensembles micromega.Lia.
Require Import ExtLib.Structures.Monad.

Import ListNotations MonadNotation.

Open Scope fun_scope.
Close Scope Z_scope.

(** * Bundles with distinct function names *)

Lemma nodupb_NoDup l : nodupb l = true -> NoDup l.
Proof.
  induction l as [| x l IH]; simpl; intros H; [ constructor |].
  apply andb_prop in H as [H1 H2]. constructor; eauto.
  intros Hin. apply negb_true_iff in H1.
  assert (Hex : existsb (Pos.eqb x) l = true).
  { apply existsb_exists. exists x. split; auto. apply Pos.eqb_refl. }
  congruence.
Qed.

Lemma NoDup_nodupb l : NoDup l -> nodupb l = true.
Proof.
  induction 1; simpl; auto. rewrite IHNoDup, andb_true_r.
  apply negb_true_iff. destruct (existsb (Pos.eqb x) l) eqn:Hex; auto.
  apply existsb_exists in Hex as [y [Hy Heq]]. apply Pos.eqb_eq in Heq. subst. contradiction.
Qed.

Lemma name_in_fundefs_all_fun_name B : name_in_fundefs B <--> FromList (all_fun_name B).
Proof.
  induction B; simpl; repeat normalize_sets; [| reflexivity ].
  rewrite IHB. reflexivity.
Qed.

Lemma unique_bindings_fnd :
  (forall e, unique_bindings e -> fnd e = true) /\
  (forall B, unique_bindings_fundefs B -> fnd_fds B = true /\ NoDup (all_fun_name B)).
Proof.
  eapply exp_def_mutual_ind.
  - intros ? ? ? ? IH H; inv H; simpl; eauto.
  - intros; reflexivity.
  - intros v l c e IHe IHl H. inv H. simpl.
    rewrite IHe by assumption. simpl. exact (IHl ltac:(assumption)).
  - intros ? ? ? ? ? IH H; inv H; simpl; eauto.
  - intros ? ? ? ? ? IH H; inv H; simpl; eauto.
  - intros B IHB e IHe H. inv H. simpl. destruct (IHB ltac:(assumption)) as [Hf1 Hf2].
    rewrite Hf1, IHe, NoDup_nodupb; auto.
  - intros; reflexivity.
  - intros ? ? ? IH H; inv H; simpl; eauto.
  - intros ? ? ? ? IH H; inv H; simpl; eauto.
  - intros; reflexivity.
  - intros f t xs e IHe B IHB H. inv H. destruct (IHB ltac:(assumption)) as [Hf1 Hf2]. simpl.
    rewrite IHe, Hf1 by assumption. split; [ reflexivity |]. constructor; auto. intros Hin.
    match goal with Hn : ~ bound_var_fundefs _ _ |- _ => apply Hn end.
    eapply name_in_fundefs_bound_var_fundefs. eapply name_in_fundefs_all_fun_name. exact Hin.
  - split; [ reflexivity | constructor ].
Qed.

(** * Renamings *)

Definition below (S : Ensemble var) (n : positive) := forall z, z \in S -> (z < n)%positive.

Definition sig_below (sigma : M.t positive) (n : positive) :=
  forall z y, M.get z sigma = Some y -> (y < n)%positive.

Lemma below_mon S S' n n' : S \subset S' -> (n <= n')%positive -> below S' n -> below S n'.
Proof. intros H1 H2 H3 z Hz. specialize (H3 z (H1 z Hz)). lia. Qed.

Lemma below_Union S1 S2 n : below (S1 :|: S2) n -> below S1 n /\ below S2 n.
Proof. intros H. split; intros z Hz; eapply H; eauto. Qed.

Lemma sig_below_mon sigma n n' : (n <= n')%positive -> sig_below sigma n -> sig_below sigma n'.
Proof. intros H1 H2 z y Hz. eapply H2 in Hz. lia. Qed.

Lemma sig_below_set sigma x y n : sig_below sigma n -> (y < n)%positive -> sig_below (M.set x y sigma) n.
Proof. intros H1 H2 z y' Hz. rewrite M.gsspec in Hz. destruct (peq z x); [ congruence | eauto ]. Qed.

Lemma apply_r_below sigma S n z :
  sig_below sigma n -> below S n -> z \in S -> (apply_r sigma z < n)%positive.
Proof.
  intros H1 H2 Hz. unfold apply_r. match goal with |- context [ match ?m with _ => _ end ] => destruct m eqn:Hg end; [ exact (H1 _ _ Hg) | exact (H2 _ Hz) ].
Qed.

Lemma apply_r_set sigma x y : f_eq (apply_r (M.set x y sigma)) ((apply_r sigma) {x ~> y}).
Proof.
  intros z. unfold apply_r, extend. rewrite M.gsspec. destruct (peq z x); reflexivity.
Qed.

Lemma apply_r_empty : f_eq (apply_r (M.empty positive)) id.
Proof. intros z. unfold apply_r. rewrite M.gempty. reflexivity. Qed.

Lemma set_lists_apply_r xs ys s s' :
  set_lists xs ys s = Some s' ->
  forall z, (List.In z xs /\ List.In (apply_r s' z) ys) \/ (~ List.In z xs /\ apply_r s' z = apply_r s z).
Proof.
  revert ys s'. induction xs as [| x xs IH]; intros ys s' Hs z; destruct ys as [| y ys]; simpl in Hs; try discriminate.
  - inv Hs. right. split; auto.
  - destruct (set_lists xs ys s) as [s1 |] eqn:Hs1; inv Hs.
    rewrite (apply_r_set s1 x y z). unfold extend. destruct (peq z x).
    + subst. left. split; left; reflexivity.
    + destruct (IH _ _ Hs1 z) as [[H1 H2] | [H1 H2]].
      * left. split; right; assumption.
      * right. split; [ intros [Hc | Hc]; [ congruence | contradiction ] | exact H2 ].
Qed.

Lemma sig_below_set_lists xs ys s s' n :
  set_lists xs ys s = Some s' -> sig_below s n -> (forall y, List.In y ys -> (y < n)%positive) ->
  sig_below s' n.
Proof.
  revert ys s'. induction xs as [| x xs IH]; intros ys s' Hs H1 H2; destruct ys as [| y ys]; simpl in Hs; try discriminate.
  - inv Hs. assumption.
  - destruct (set_lists xs ys s) as [s1 |] eqn:Hs1; inv Hs.
    eapply sig_below_set; [ eapply IH; eauto; intros; eapply H2; right; auto | eapply H2; left; auto ].
Qed.

Lemma set_lists_injective xs ys s s' :
  set_lists xs ys s = Some s' -> NoDup ys -> injective_subdomain (FromList xs) (apply_r s').
Proof.
  revert ys s'. induction xs as [| x xs IH]; intros ys s' Hs Hnd; destruct ys as [| y ys]; simpl in Hs; try discriminate.
  - inv Hs. intros z1 z2 Hz. inv Hz.
  - destruct (set_lists xs ys s) as [s1 |] eqn:Hs1; inv Hs. inv Hnd.
    intros z1 z2 Hz1 Hz2 Heq. rewrite !apply_r_set in Heq. unfold extend in Heq.
    destruct (peq z1 x); destruct (peq z2 x); subst; auto.
    + exfalso. eapply H1. destruct (set_lists_apply_r _ _ _ _ Hs1 z2) as [[_ Hin] | [Hn _]]; [ exact Hin |].
      exfalso. inv Hz2; [ congruence | contradiction ].
    + exfalso. eapply H1. destruct (set_lists_apply_r _ _ _ _ Hs1 z1) as [[_ Hin] | [Hn _]]; [ exact Hin |].
      exfalso. inv Hz1; [ congruence | contradiction ].
    + eapply IH; eauto.
      * inv Hz1; [ congruence | assumption ].
      * inv Hz2; [ congruence | assumption ].
Qed.

Lemma construct_lst_exists xs ys s s' :
  set_lists xs ys s = Some s' -> NoDup ys ->
  exists f', construct_lst_injection (apply_r s) xs ys f' /\ f_eq f' (apply_r s').
Proof.
  revert ys s'. induction xs as [| x xs IH]; intros ys s' Hs Hnd; destruct ys as [| y ys]; simpl in Hs; try discriminate.
  - inv Hs. eexists. split; [ constructor | reflexivity ].
  - destruct (set_lists xs ys s) as [s1 |] eqn:Hs1; inv Hs. inv Hnd.
    destruct (IH _ _ Hs1 H2) as [f1 [Hc Hf]].
    exists (f1 {x ~> y}). split.
    + constructor; auto.
      eapply injective_subdomain_f_eq_subdomain.
      * eapply (set_lists_injective (x :: xs) (y :: ys) s (M.set x y s1)); simpl; [ rewrite Hs1; reflexivity | constructor; auto ].
      * intros z _. rewrite apply_r_set. unfold extend. destruct (peq z x); auto.
    + intros z. rewrite apply_r_set. unfold extend. destruct (peq z x); auto.
Qed.

Lemma construct_fundefs_exists (h f : var -> var) B B' :
  all_fun_name B' = map h (all_fun_name B) ->
  injective_subdomain (name_in_fundefs B) h ->
  exists f', construct_fundefs_injection f B B' f' /\
             (forall z, z \in name_in_fundefs B -> f' z = h z) /\
             (forall z, ~ z \in name_in_fundefs B -> f' z = f z).
Proof.
  revert B'. induction B as [g t xs e B IH |]; intros B' Hn Hinj; destruct B' as [g' t' xs' e' B' |]; simpl in Hn; try discriminate.
  - injection Hn as Hg' Hn. subst g'. edestruct (IH B') as [f1 [Hc [Hin1 Hin2]]]; eauto.
    { eapply injective_subdomain_antimon; [ eassumption | simpl; sets ]. }
    exists (f1 {g ~> h g}). split; [| split ].
    + constructor; auto.
      eapply injective_subdomain_f_eq_subdomain; [ eassumption |].
      intros z Hz. unfold extend. destruct (peq z g); [ subst; reflexivity |].
      rewrite Hin1; auto. destruct Hz as [z Hz | z Hz]; [ inv Hz; congruence | assumption ].
    + intros z Hz. unfold extend. destruct (peq z g); [ subst; reflexivity |].
      eapply Hin1. destruct Hz as [z Hz | z Hz]; [ inv Hz; congruence | assumption ].
    + intros z Hz. unfold extend. destruct (peq z g); [ subst; exfalso; eapply Hz; left; reflexivity |].
      eapply Hin2. intros Hc'. eapply Hz. right. assumption.
  - exists f. split; [ constructor | split; [ intros z Hz; inv Hz | reflexivity ] ].
Qed.

Lemma NoDup_map_inj (h : var -> var) l :
  injective_subdomain (FromList l) h -> NoDup l -> NoDup (map h l).
Proof.
  induction l as [| x l IH]; simpl; intros Hinj Hnd; constructor; inv Hnd.
  - intros Hin. apply in_map_iff in Hin as [y [Heq Hy]].
    assert (x = y) by (eapply Hinj; [ left; reflexivity | right; exact Hy | auto ]). subst. contradiction.
  - eapply IH; auto. eapply injective_subdomain_antimon; [ eassumption | normalize_sets; sets ].
Qed.

Lemma Forall2_map_eq (f : var -> var) l : Forall2 (fun y y' => f y = y') l (map f l).
Proof. induction l; constructor; auto. Qed.

Lemma below_same S S' n : S <--> S' -> below S n -> below S' n.
Proof. intros [_ H] Hb z Hz. eapply Hb. eapply H. exact Hz. Qed.

Definition inr (a b : positive) (S : Ensemble var) := forall z, z \in S -> (a <= z < b)%positive.

(** * The state monad, at a given state *)

Definition W := (comp_data * unit)%type.
Definition nv (w : W) : positive := next_var (fst w).
Definition at_st (w : W) : unit -> W -> Prop := fun _ w' => w' = w.

Lemma bind_at {A B} (m : freshM A) (k : A -> freshM B) w (Q' : A -> W -> Prop) (Q : B -> W -> Prop) :
  {{ at_st w }} m {{ fun _ _ x w' => Q' x w' }} ->
  (forall x w', Q' x w' -> {{ at_st w' }} k x {{ fun _ _ y w'' => Q y w'' }}) ->
  {{ at_st w }} (x <- m;; k x) {{ fun _ _ y w'' => Q y w'' }}.
Proof.
  intros H1 H2. eapply bind_triple; [ exact H1 |].
  intros x w0. unfold triple. intros r w' HQ. exact (H2 x w' HQ r w' eq_refl).
Qed.

Lemma ret_at {A} (x : A) w (Q : A -> W -> Prop) : Q x w -> {{ at_st w }} ret x {{ fun _ _ y w' => Q y w' }}.
Proof. intros H. eapply return_triple. intros r w' Hw. unfold at_st in Hw. subst. exact H. Qed.

Lemma get_name_at x str w :
  {{ at_st w }} get_name x str {{ fun _ _ x' w' => (nv w <= x' < nv w')%positive }}.
Proof.
  unfold triple. intros r w0 Hw. unfold at_st in Hw. subst w0.
  pose proof (get_name_spec unit (Full_set var) x str r w (fun y _ => Full_intro _ y)) as H.
  revert H. unfold nv. destruct (runState _ _ _) as [[| x'] w']; simpl; auto.
  intros [_ [H _]]. exact H.
Qed.

Lemma get_names_lst_at xs str w :
  {{ at_st w }} get_names_lst xs str
  {{ fun _ _ ys w' => NoDup ys /\ length ys = length xs /\
                      (forall y, List.In y ys -> (nv w <= y < nv w')%positive) /\ (nv w <= nv w')%positive }}.
Proof.
  unfold triple. intros r w0 Hw. unfold at_st in Hw. subst w0.
  pose proof (get_names_lst_spec unit (Full_set var) xs str r w (fun y _ => Full_intro _ y)) as H.
  revert H. unfold nv. destruct (runState _ _ _) as [[| ys] w']; simpl; auto.
  intros [H1 [H2 [_ [H4 [H5 _]]]]]. split; [| split; [| split ]]; auto.
Qed.

Definition freshen_br (sigma : M.t positive) :=
  fix alpha_list (pats : list (ctor_tag * exp)) : freshM (list (ctor_tag * exp)) :=
    match pats with
    | nil => ret nil
    | pat :: pats =>
        let '(t, e) := pat in
        e' <- freshen_term e sigma ;;
        pats' <- alpha_list pats ;;
        ret ((t, e') :: pats')
    end.

Lemma freshen_term_Ecase v cl sigma :
  freshen_term (Ecase v cl) sigma = (cl' <- freshen_br sigma cl;; ret (Ecase (apply_r sigma v) cl')).
Proof. reflexivity. Qed.

Definition FPost (sigma : M.t positive) (e : exp) (w : W) (e' : exp) (w' : W) :=
  Alpha_conv e e' (apply_r sigma) /\ (nv w <= nv w')%positive /\
  inr (nv w) (nv w') (bound_var e') /\ (fnd e = true -> unique_bindings e').

Definition FPost_fds (sigma : M.t positive) (B : fundefs) (w : W) (B' : fundefs) (w' : W) :=
  Alpha_conv_fundefs B B' (apply_r sigma) /\ all_fun_name B' = map (apply_r sigma) (all_fun_name B) /\
  (nv w <= nv w')%positive /\ inr (nv w) (nv w') (bound_var_fundefs B' \\ name_in_fundefs B') /\
  (fnd_fds B = true -> NoDup (all_fun_name B') -> unique_bindings_fundefs B').

Lemma Alpha_conv_set e e' sigma x x' :
  Alpha_conv e e' (apply_r (M.set x x' sigma)) -> Alpha_conv e e' ((apply_r sigma) {x ~> x'}).
Proof. intros H. eapply (proj1 (Alpha_conv_proper _ _ eq_refl _ _ eq_refl _ _ (apply_r_set sigma x x'))). exact H. Qed.

Lemma fresh_not_in_image sigma e n x' :
  sig_below sigma n -> below (used_vars e) n -> (n <= x')%positive ->
  ~ x' \in image (apply_r sigma) (occurs_free e) :|: bound_var e.
Proof.
  intros Hs Hb Hx Hc. inversion Hc as [z Hz Hzx | z Hz Hzx]; subst z.
  - destruct Hz as [y [Hy Heq]]. rewrite <- Heq in Hx.
    assert (apply_r sigma y < n)%positive by (eapply (apply_r_below sigma (used_vars e)); [ exact Hs | exact Hb | unfold used_vars; right; exact Hy ]).
    exact (Pos.lt_irrefl _ (Pos.le_lt_trans _ _ _ Hx H)).
  - assert (x' < n)%positive by (eapply Hb; unfold used_vars; left; exact Hz).
    exact (Pos.lt_irrefl _ (Pos.le_lt_trans _ _ _ Hx H)).
Qed.

Lemma inr_split B' a b z :
  inr a b (bound_var_fundefs B' \\ name_in_fundefs B') -> z \in bound_var_fundefs B' ->
  z \in name_in_fundefs B' \/ (a <= z < b)%positive.
Proof.
  intros H Hz. destruct (@Dec _ _ (Decidable_name_in_fundefs B') z); [ left; auto | right; apply H; constructor; auto ].
Qed.

Lemma used_vars_fundefs_names B : name_in_fundefs B \subset used_vars_fundefs B.
Proof. unfold used_vars_fundefs. eapply Included_Union_preserv_l. apply name_in_fundefs_bound_var_fundefs. Qed.

Lemma below_names B B' sigma n :
  all_fun_name B' = map (apply_r sigma) (all_fun_name B) -> sig_below sigma n ->
  below (used_vars_fundefs B) n -> below (name_in_fundefs B') n.
Proof.
  intros Hn Hs Hb z Hz. apply (proj1 (name_in_fundefs_all_fun_name B')) in Hz.
  rewrite Hn in Hz. unfold FromList, Ensembles.In in Hz. apply in_map_iff in Hz as [y [Heq Hy]]. subst.
  eapply apply_r_below; [ exact Hs | exact Hb |]. eapply used_vars_fundefs_names.
  apply (proj2 (name_in_fundefs_all_fun_name B)). exact Hy.
Qed.

Lemma names_in_ns B B' sigma sigma' ns :
  set_lists (all_fun_name B) ns sigma = Some sigma' ->
  all_fun_name B' = map (apply_r sigma') (all_fun_name B) ->
  forall z, z \in name_in_fundefs B' -> List.In z ns.
Proof.
  intros Hsl Hn z Hz. apply (proj1 (name_in_fundefs_all_fun_name B')) in Hz.
  rewrite Hn in Hz. unfold FromList, Ensembles.In in Hz. apply in_map_iff in Hz as [y [Heq Hy]]. subst.
  destruct (set_lists_apply_r _ _ _ _ Hsl y) as [[_ H] | [H _]]; [ exact H | contradiction ].
Qed.

Lemma bound_var_Ecase_any x y l z : bound_var (Ecase x l) z -> bound_var (Ecase y l) z.
Proof. intros H. inv H. econstructor; eauto. Qed.

Lemma bv_Fcons_cases g t xs e B z :
  z \in bound_var_fundefs (Fcons g t xs e B) ->
  z = g \/ List.In z xs \/ z \in bound_var e \/ z \in bound_var_fundefs B.
Proof.
  intros H. inversion H; subst; auto.
  match goal with Hu : _ \in Union _ _ _ |- _ => inv Hu end; [ match goal with Hs : _ \in [set _] |- _ => inv Hs end | ]; auto.
Qed.

Lemma freshen_br_nil sigma : freshen_br sigma [] = ret [].
Proof. reflexivity. Qed.

Lemma freshen_br_cons sigma c e l :
  freshen_br sigma ((c, e) :: l) =
  (e' <- freshen_term e sigma;; pats' <- freshen_br sigma l;; ret ((c, e') :: pats')).
Proof. reflexivity. Qed.

Ltac fresh_bind uv e IH w Hb Hs :=
  eapply bind_at; [ eapply get_name_at |]; intros x' w1 Hx; cbv beta in Hx;
  assert (Hbe : below (used_vars e) (nv w))
    by (eapply below_mon; [| apply Pos.le_refl | exact Hb ]; rewrite uv; sets);
  eapply bind_at; [ eapply IH; [ eapply below_mon; [ reflexivity | | exact Hbe ]; lia
                               | eapply sig_below_set; [ eapply sig_below_mon; [| exact Hs ]; lia | lia ] ] |];
  intros e' w2 Hp; cbv beta in Hp; destruct Hp as [Ha [Hn [Hbv Hub]]];
  eapply ret_at; split; [| split; [| split ]];
  [ constructor; first [ eapply Forall2_map_eq | reflexivity
                       | eapply fresh_not_in_image; [ exact Hs | exact Hbe | lia ]
                       | eapply Alpha_conv_set; exact Ha ]
  | lia
  | intros z Hz; inv Hz; [ lia | match goal with H : bound_var e' z |- _ => eapply Hbv in H end; lia ]
  | intros Hf; simpl in Hf; constructor; [ intros Hc; eapply Hbv in Hc; lia | eauto ] ].

Lemma freshen_correct_mut :
  (forall e sigma w, below (used_vars e) (nv w) -> sig_below sigma (nv w) ->
     {{ at_st w }} freshen_term e sigma {{ fun _ _ e' w' => FPost sigma e w e' w' }}) /\
  (forall B sigma w, below (used_vars_fundefs B) (nv w) -> sig_below sigma (nv w) ->
     {{ at_st w }} freshen_fun B sigma {{ fun _ _ B' w' => FPost_fds sigma B w B' w' }}).
Proof.
  eapply exp_def_mutual_ind'.
  - (* Econstr *)
    intros x t ys e IH sigma w Hb Hs. cbn [freshen_term]. fresh_bind used_vars_Econstr e IH w Hb Hs.
  - (* Ecase *)
    intros v l Hall sigma w Hb Hs. rewrite freshen_term_Ecase.
    eapply bind_at with
      (Q' := fun l' w' =>
               Forall2 (fun p p' => fst p = fst p' /\ Alpha_conv (snd p) (snd p') (apply_r sigma)) l l' /\
               (nv w <= nv w')%positive /\ inr (nv w) (nv w') (bound_var (Ecase v l')) /\
               (forallb (fun p => fnd (snd p)) l = true -> forall y, unique_bindings (Ecase y l'))).
    + revert w Hb Hs.
      induction Hall as [| [c e] l He Hl IHl]; intros w Hb Hs'.
      * rewrite freshen_br_nil. eapply ret_at. split; [ constructor | split; [ lia | split ] ].
        -- intros z Hz. rewrite bound_var_Ecase_nil in Hz. inv Hz.
        -- intros _ y. constructor.
      * simpl in He. rewrite freshen_br_cons.
        apply (below_same _ _ _ (used_vars_Ecase_cons _ _ _ _)) in Hb. apply below_Union in Hb as [Hb1 Hb2].
        eapply bind_at; [ eapply He; eassumption |]. intros e' w1 Hp. cbv beta in Hp. destruct Hp as [Ha [Hn [Hbv Hub]]].
        eapply bind_at; [ eapply IHl; [ eapply below_mon; [ reflexivity | | exact Hb2 ]; lia | eapply sig_below_mon; [| exact Hs' ]; lia ] |].
        intros l' w2 Hp. cbv beta in Hp. destruct Hp as [HF [Hn' [Hbv' Hub']]].
        eapply ret_at. split; [| split; [| split ]].
        -- constructor; [ split; [ reflexivity | exact Ha ] | exact HF ].
        -- lia.
        -- intros z Hz. rewrite bound_var_Ecase_cons in Hz. inv Hz.
           ++ eapply Hbv in H. lia.
           ++ eapply Hbv' in H. lia.
        -- intros Hf y. simpl in Hf. apply andb_prop in Hf as [Hf1 Hf2]. constructor; eauto.
           constructor. intros z Hz. inv Hz. eapply Hbv in H. eapply bound_var_Ecase_any in H0. eapply Hbv' in H0. lia.
    + intros l' w' Hp. cbv beta in Hp. destruct Hp as [HF [Hn [Hbv Hub]]].
      eapply ret_at. split; [| split; [| split ]].
      * constructor; [ exact HF | reflexivity ].
      * exact Hn.
      * intros z Hz. eapply Hbv. eapply bound_var_Ecase_any. exact Hz.
      * intros Hf. eapply Hub. exact Hf.
  - (* Eproj *)
    intros x t n y e IH sigma w Hb Hs. cbn [freshen_term]. fresh_bind used_vars_Eproj e IH w Hb Hs.
  - (* Eletapp *)
    intros x f ft ys e IH sigma w Hb Hs. cbn [freshen_term]. fresh_bind used_vars_Eletapp e IH w Hb Hs.
  - (* Efun *)
    intros B IHB e IHe sigma w Hb Hs. cbn [freshen_term].
    assert (Hb0 := Hb). apply (below_same _ _ _ (used_vars_Efun _ _)) in Hb. apply below_Union in Hb as [HbB Hbe].
    eapply bind_at; [ eapply get_names_lst_at |]. intros ns w1 Hp. cbv beta in Hp. destruct Hp as [Hnd [Hlen [Hns Hn1]]].
    match goal with |- context [ set_lists ?a ?b ?c ] => destruct (set_lists a b c) as [sigma' |] eqn:Hsl end;
      [| exfalso; destruct (set_lists_length3 sigma (all_fun_name B) ns (eq_sym Hlen)) as [s2 Hs2];
         assert (Hc0 : Some s2 = None) by (rewrite <- Hs2; exact Hsl); discriminate ].
    assert (Hs' : sig_below sigma' (nv w1))
      by (eapply sig_below_set_lists; [ exact Hsl | eapply sig_below_mon; [| exact Hs ]; lia | intros y Hy; apply Hns in Hy; lia ]).
    eapply bind_at; [ eapply IHB; [ eapply below_mon; [ reflexivity | | exact HbB ]; lia | exact Hs' ] |].
    intros B' w2 Hp. cbv beta in Hp. destruct Hp as [HaB [Hnames [Hn2 [HbvB HubB]]]].
    eapply bind_at; [ eapply IHe; [ eapply below_mon; [ reflexivity | | exact Hbe ]; lia | eapply sig_below_mon; [| exact Hs' ]; lia ] |].
    intros e' w3 Hp. cbv beta in Hp. destruct Hp as [Ha [Hn3 [Hbv Hub]]].
    assert (Hinj : injective_subdomain (name_in_fundefs B) (apply_r sigma')).
    { eapply injective_subdomain_antimon; [ eapply set_lists_injective; eassumption | apply (proj1 (name_in_fundefs_all_fun_name B)) ]. }
    destruct (construct_fundefs_exists (apply_r sigma') (apply_r sigma) B B' Hnames Hinj) as [f' [Hc [Hf1 Hf2]]].
    assert (Hfeq : f_eq f' (apply_r sigma')).
    { intros z. destruct (set_lists_apply_r _ _ _ _ Hsl z) as [[Hin _] | [Hnin Heq]].
      - eapply Hf1. apply (proj2 (name_in_fundefs_all_fun_name B)). exact Hin.
      - rewrite Hf2; [ symmetry; exact Heq | intros Hc'; apply Hnin; apply (proj1 (name_in_fundefs_all_fun_name B)); exact Hc' ]. }
    assert (HnB' : forall z, z \in name_in_fundefs B' -> (nv w <= z < nv w1)%positive)
      by (intros z Hz; eapply Hns; eapply names_in_ns; eassumption).
    assert (HbvB' : forall z, z \in bound_var_fundefs B' -> (nv w <= z < nv w2)%positive).
    { intros z Hz. destruct (inr_split _ _ _ _ HbvB Hz) as [H | H]; [ apply HnB' in H |]; lia. }
    eapply ret_at. split; [| split; [| split ]].
    + econstructor.
      * constructor. intros z Hz. inv Hz. apply HnB' in H.
        eapply (fresh_not_in_image sigma (Efun B e) (nv w) z Hs Hb0); [ lia | exact H0 ].
      * exact Hc.
      * eapply (proj2 (Alpha_conv_fundfes_proper _ _ eq_refl _ _ eq_refl _ _ Hfeq)). exact HaB.
      * eapply (proj2 (Alpha_conv_proper _ _ eq_refl _ _ eq_refl _ _ Hfeq)). exact Ha.
    + lia.
    + intros z Hz. inv Hz;
        match goal with
        | H : bound_var_fundefs _ _ |- _ => apply HbvB' in H; lia
        | H : bound_var _ _ |- _ => apply Hbv in H; lia
        end.
    + intros Hf. simpl in Hf. apply andb_prop in Hf as [Hf Hfe]. apply andb_prop in Hf as [Hnodup HfB].
      constructor.
      * eauto.
      * eapply HubB; [ exact HfB |]. rewrite Hnames.
        eapply NoDup_map_inj; [ eapply set_lists_injective; eassumption | eapply nodupb_NoDup; exact Hnodup ].
      * constructor. intros z Hz. inv Hz. apply Hbv in H. apply HbvB' in H0. lia.
  - (* Eapp *)
    intros f t ys sigma w Hb Hs. cbn [freshen_term]. eapply ret_at. split; [| split; [| split ]].
    + constructor; [ eapply Forall2_map_eq | reflexivity ].
    + lia.
    + intros z Hz. inv Hz.
    + intros _. constructor.
  - (* Eprim_val *)
    intros x p e IH sigma w Hb Hs. cbn [freshen_term]. fresh_bind used_vars_Eprim_val e IH w Hb Hs.
  - (* Eprim *)
    intros x p ys e IH sigma w Hb Hs. cbn [freshen_term]. fresh_bind used_vars_Eprim e IH w Hb Hs.
  - (* Ehalt *)
    intros x sigma w Hb Hs. cbn [freshen_term]. eapply ret_at. split; [| split; [| split ]].
    + constructor. reflexivity.
    + lia.
    + intros z Hz. inv Hz.
    + intros _. constructor.
  - (* Fcons *)
    intros g t xs e IHe B IHB sigma w Hb Hs. cbn [freshen_fun].
    assert (Hbe : below (used_vars e) (nv w))
      by (eapply below_mon; [| apply Pos.le_refl | exact Hb ]; rewrite used_vars_Fcons; sets).
    assert (HbB : below (used_vars_fundefs B) (nv w))
      by (eapply below_mon; [| apply Pos.le_refl | exact Hb ]; rewrite used_vars_Fcons; sets).
    assert (Hg : (apply_r sigma g < nv w)%positive).
    { eapply apply_r_below; [ exact Hs | exact Hb |]. eapply used_vars_fundefs_names. simpl. left. constructor. }
    eapply bind_at; [ eapply get_names_lst_at |]. intros xs' w1 Hp. cbv beta in Hp. destruct Hp as [Hnd [Hlen [Hxs Hn1]]].
    match goal with |- context [ set_lists ?a ?b ?c ] => destruct (set_lists a b c) as [sigma' |] eqn:Hsl end;
      [| exfalso; destruct (set_lists_length3 sigma xs xs' (eq_sym Hlen)) as [s2 Hs2];
         assert (Hc0 : Some s2 = None) by (rewrite <- Hs2; exact Hsl); discriminate ].
    eapply bind_at; [ eapply IHe; [ eapply below_mon; [ reflexivity | | exact Hbe ]; lia
                                  | eapply sig_below_set_lists; [ exact Hsl | eapply sig_below_mon; [| exact Hs ]; lia
                                                                | intros y Hy; apply Hxs in Hy; lia ] ] |].
    intros e' w2 Hp. cbv beta in Hp. destruct Hp as [Ha [Hn2 [Hbv Hub]]].
    eapply bind_at; [ eapply IHB; [ eapply below_mon; [ reflexivity | | exact HbB ]; lia | eapply sig_below_mon; [| exact Hs ]; lia ] |].
    intros B' w3 Hp. cbv beta in Hp. destruct Hp as [HaB [Hnames [Hn3 [HbvB HubB]]]].
    destruct (construct_lst_exists _ _ _ _ Hsl Hnd) as [f'' [Hc Hfeq]].
    assert (HnB' : below (name_in_fundefs B') (nv w)) by (eapply below_names; eassumption).
    assert (HbvB' : forall z, z \in bound_var_fundefs B' -> (z < nv w)%positive \/ (nv w2 <= z < nv w3)%positive).
    { intros z Hz. destruct (inr_split _ _ _ _ HbvB Hz) as [H | H]; [ left; apply HnB'; exact H | right; exact H ]. }
    eapply ret_at. split; [| split; [| split; [| split ]]].
    + econstructor.
      * reflexivity.
      * exact HaB.
      * constructor. intros z Hz. inv Hz. apply Hxs in H.
        eapply (fresh_not_in_image sigma e (nv w) z Hs Hbe); [ lia | exact H0 ].
      * exact Hc.
      * eapply (proj2 (Alpha_conv_proper _ _ eq_refl _ _ eq_refl _ _ Hfeq)). exact Ha.
    + simpl. rewrite Hnames. reflexivity.
    + lia.
    + intros z [Hz Hnz]. destruct (bv_Fcons_cases _ _ _ _ _ _ Hz) as [Hz' | [Hz' | [Hz' | Hz']]].
      * subst. exfalso. apply Hnz. simpl. left. constructor.
      * apply Hxs in Hz'. lia.
      * apply Hbv in Hz'. lia.
      * assert (Hz2 : (nv w2 <= z < nv w3)%positive).
        { apply HbvB. constructor; [ exact Hz' | intros Hc'; apply Hnz; simpl; right; exact Hc' ]. }
        lia.
    + intros Hf HND. simpl in Hf, HND. apply andb_prop in Hf as [Hfe HfB].
      apply NoDup_cons_iff in HND as [HND1 HND2].
      constructor.
      * intros Hc'. apply Hbv in Hc'. lia.
      * intros Hc'. destruct (inr_split _ _ _ _ HbvB Hc') as [H | H]; [| lia ].
        apply HND1. apply (proj1 (name_in_fundefs_all_fun_name B')). exact H.
      * constructor. intros z Hz. inv Hz. apply Hbv in H. apply Hxs in H0. lia.
      * constructor. intros z Hz. inv Hz. apply Hxs in H0. destruct (HbvB' _ H); lia.
      * constructor. intros z Hz. inv Hz. apply Hbv in H. destruct (HbvB' _ H0); lia.
      * intros Hc'. apply Hxs in Hc'. lia.
      * exact Hnd.
      * eauto.
      * eauto.
  - (* Fnil *)
    intros sigma w Hb Hs. cbn [freshen_fun]. eapply ret_at. split; [| split; [| split; [| split ]]].
    + constructor.
    + reflexivity.
    + lia.
    + intros z [Hz _]. inv Hz.
    + intros _ _. constructor.
Qed.

(** * The top level *)

Lemma injective_subdomain_id (S : Ensemble var) : injective_subdomain S (@id var).
Proof. intros x y _ _ H. exact H. Qed.

Theorem freshen_top_correct e c :
  (max_var e 1 < next_var c)%positive ->
  fnd e = true ->
  exists e' c',
    freshen_top e c = (Ret e', c') /\
    Alpha_conv e e' id /\
    unique_bindings e' /\
    Disjoint _ (bound_var e') (occurs_free e') /\
    occurs_free e' <--> occurs_free e /\
    (max_var e' 1 < next_var c')%positive.
Proof.
  intros Hmax Hf.
  assert (Hb : below (used_vars e) (nv (c, tt))).
  { intros z [z' Hz | z' Hz]; unfold nv; simpl.
    - eapply Pos.le_lt_trans; [ eapply (proj1 bound_var_leq_max_var_mut); exact Hz | exact Hmax ].
    - eapply Pos.le_lt_trans; [ eapply (proj1 occurs_free_leq_max_var_mut); exact Hz | exact Hmax ]. }
  assert (Hs : sig_below (M.empty positive) (nv (c, tt))) by (intros z y Hz; rewrite M.gempty in Hz; discriminate).
  pose proof (proj1 freshen_correct_mut e (M.empty _) (c, tt) Hb Hs tt (c, tt) eq_refl) as H.
  unfold freshen_top, run_compM. revert H.
  destruct (runState _ _ _) as [[| e'] [c' []]]; [ contradiction |]. intros [Ha [Hn [Hbv Hub]]].
  unfold nv in *; simpl in *.
  assert (Ha' : Alpha_conv e e' id) by (eapply (proj1 (Alpha_conv_proper _ _ eq_refl _ _ eq_refl _ _ apply_r_empty)); exact Ha).
  assert (Hfv : occurs_free e' <--> occurs_free e).
  { rewrite <- (Alpha_conv_occurs_free _ _ _ Ha' (injective_subdomain_id _)). eapply image_id. }
  exists e', c'. split; [ reflexivity |]. split; [ exact Ha' |]. split; [ eauto |].
  split; [| split; [ exact Hfv |]].
  - constructor. intros z Hz. inv Hz. apply Hbv in H. apply Hfv in H0.
    assert (z < next_var c)%positive by (eapply Hb; right; exact H0). lia.
  - destruct (max_var_subset e') as [z Hz | z Hz].
    + apply Hbv in Hz. lia.
    + apply Hfv in Hz. assert (z < next_var c)%positive by (eapply Hb; right; exact Hz). lia.
Qed.

Require Import LambdaANF.algebra LambdaANF.eval LambdaANF.logical_relations.

Section Sem.

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  (** α-equivalence under the identity on the free variables refines *)
  Lemma Alpha_conv_id_preord cenv (P : PostT) (PG : PostGT) e e' k rho1 rho2 :
    Post_properties cenv P P PG ->
    Alpha_conv e e' id ->
    preord_env_P cenv PG (occurs_free e) k rho1 rho2 ->
    preord_exp cenv P PG k (e, rho1) (e', rho2).
  Proof.
    intros Hp Ha Henv. eapply Alpha_conv_correct; eauto. eapply injective_subdomain_id.
  Qed.

End Sem.
