(* The solver never runs out of fuel.

   Every operation of a round only adds to the state, so the size of the
   state within the universe of the program (its variables, labels and
   arities) grows with every round that changes it.  That size is bounded,
   and the fuel of the solver is one more than the bound, so the solver
   always reaches a round that changes nothing ([solve_some]).  Likewise,
   each pass merging internal webs only lowers them, so the merge always
   stabilizes ([merge_done]). *)

From Stdlib Require Import NArith ZArith.ZArith Lists.List Bool micromega.Lia
     MSets.MSetDecide MSets.MSetProperties SetoidList.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import set_util.
From CertiRocq.LambdaANF Require term.
From CertiRocq.LambdaWeb Require Import syntax.
From CertiRocq.LambdaCFA Require Import spec impl.

Import ListNotations.
Local Open Scope nat_scope.

Module PSD := MSetDecide.Decide PS.
Module PSP := MSetProperties.Properties PS.

(** * Iteration with binary fuel *)

Section Loop.

  Context {A : Type} (f : A -> A) (stop : A -> A -> bool) (mu : A -> nat).
  Hypothesis (Hdec : forall a, stop a (f a) = false -> mu (f a) < mu a).

  Lemma loop1_more a a' : loop1 f stop a = More a' -> mu a' + 1 <= mu a.
  Proof.
    unfold loop1. destruct (stop a (f a)) eqn:Hs; intros H; inv H.
    specialize (Hdec a Hs). lia.
  Qed.

  Lemma loop_more p : forall a a', loop f stop p a = More a' -> mu a' + Pos.to_nat p <= mu a.
  Proof.
    induction p; intros a a' H; simpl in H.
    - rewrite Pos2Nat.inj_xI.
      destruct (loop1 f stop a) as [? | a1] eqn:H1; [ discriminate |]. simpl in H.
      destruct (loop f stop p a1) as [? | a2] eqn:H2; [ discriminate |]. simpl in H.
      apply loop1_more in H1. apply IHp in H2. apply IHp in H. lia.
    - rewrite Pos2Nat.inj_xO.
      destruct (loop f stop p a) as [? | a1] eqn:H1; [ discriminate |]. simpl in H.
      apply IHp in H1. apply IHp in H. lia.
    - apply loop1_more in H. lia.
  Qed.

  (** Fuel above the measure suffices. *)
  Lemma loop_done p a : mu a < Pos.to_nat p -> exists a', loop f stop p a = Done a'.
  Proof.
    intros Hlt. destruct (loop f stop p a) as [a' | a'] eqn:H; eauto.
    apply loop_more in H. lia.
  Qed.

End Loop.

(** * Sums *)

Lemma sum_mono {A} (f g : A -> nat) l :
  (forall a, f a <= g a) -> sum f l <= sum g l.
Proof. intros H. induction l; simpl; [ lia | specialize (H a); lia ]. Qed.

Lemma sum_bound {A} (f : A -> nat) c l :
  (forall a, f a <= c) -> sum f l <= length l * c.
Proof. intros H. induction l; simpl; [ lia | specialize (H a); lia ]. Qed.

Lemma sum_strict {A} (f g : A -> nat) l :
  (forall a, f a <= g a) -> (exists a, In a l /\ f a < g a) -> sum f l < sum g l.
Proof.
  intros H (a & Ha & Hlt). induction l as [| b l IH]; [ easy |]. simpl.
  destruct Ha as [-> | Ha]; [ pose proof (sum_mono f g l H); lia |].
  specialize (H b). specialize (IH Ha). lia.
Qed.

(** * The order on states: everything grows *)

Definition lle (l l' : list PS.t) : Prop :=
  length l <= length l' /\ forall i, PS.Subset (nth i l PS.empty) (nth i l' PS.empty).

Definition le_st (s s' : st) : Prop :=
  (forall k, PS.Subset (gv (st_v s) k) (gv (st_v s') k)) /\
  (forall k, lle (gl (st_a s) k) (gl (st_a s') k)) /\
  (forall k, lle (gl (st_f s) k) (gl (st_f s') k)) /\
  (forall k, PS.Subset (gv (st_r s) k) (gv (st_r s') k)) /\
  PS.Subset (st_top s) (st_top s') /\
  PS.Subset (st_x s) (st_x s').

Lemma lle_refl l : lle l l.
Proof. split; [ lia | intros i; PSD.fsetdec ]. Qed.

Lemma lle_trans l1 l2 l3 : lle l1 l2 -> lle l2 l3 -> lle l1 l3.
Proof.
  intros [H1 H2] [H3 H4]. split; [ lia |].
  intros i. specialize (H2 i). specialize (H4 i). PSD.fsetdec.
Qed.

Lemma le_refl s : le_st s s.
Proof. repeat split; try (intros; eapply lle_refl); intros; PSD.fsetdec. Qed.

Lemma le_trans s1 s2 s3 : le_st s1 s2 -> le_st s2 s3 -> le_st s1 s3.
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6) (H1' & H2' & H3' & H4' & H5' & H6').
  repeat split.
  - intros k. specialize (H1 k). specialize (H1' k). PSD.fsetdec.
  - eapply lle_trans; eauto.
  - eapply lle_trans; eauto.
  - eapply lle_trans; eauto.
  - eapply lle_trans; eauto.
  - intros k. specialize (H4 k). specialize (H4' k). PSD.fsetdec.
  - PSD.fsetdec.
  - PSD.fsetdec.
Qed.

Lemma gv_set m x A k : gv (M.set x A m) k = if peq k x then A else gv m k.
Proof. unfold gv, getd. rewrite M.gsspec. destruct (peq k x); reflexivity. Qed.

Lemma gl_set m x l k : gl (M.set x l m) k = if peq k x then l else gl m k.
Proof. unfold gl, getd. rewrite M.gsspec. destruct (peq k x); reflexivity. Qed.

Lemma nth_nil i : nth i ([] : list PS.t) PS.empty = PS.empty.
Proof. destruct i; reflexivity. Qed.

Lemma upd_nth_lle l i A : lle l (upd_nth l i A).
Proof.
  revert i. induction l as [| B l IH]; intros i.
  - split; [ simpl; lia |]. intros j. rewrite nth_nil. PSD.fsetdec.
  - destruct i as [| i]; simpl.
    + split; [ simpl; lia |]. intros [| j]; simpl; PSD.fsetdec.
    + destruct (IH i) as [Hl Hs]. split; [ simpl; lia |].
      intros [| j]; simpl; [ PSD.fsetdec | eapply Hs ].
Qed.

Lemma expose_lle l n : lle l (map (PS.add ltop) (l ++ repeat PS.empty (n - length l))).
Proof.
  split.
  - rewrite length_map, length_app. lia.
  - intros i. destruct (Nat.lt_ge_cases i (length l)) as [Hi | Hi].
    + rewrite (nth_indep (map (PS.add ltop) (l ++ repeat PS.empty (n - length l)))
                         PS.empty (PS.add ltop PS.empty))
        by (rewrite length_map, length_app; lia).
      rewrite map_nth, app_nth1 by assumption. PSD.fsetdec.
    + rewrite nth_overflow by assumption. PSD.fsetdec.
Qed.

(** Every operation adds to the state. *)

Ltac le_simpl :=
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); simpl; intros;
  repeat match goal with
         | |- context [ gv (M.set _ _ _) _ ] => rewrite gv_set
         | |- context [ gl (M.set _ _ _) _ ] => rewrite gl_set
         | |- context [ if peq ?k ?x then _ else _ ] => destruct (peq k x); subst
         end;
  try eapply lle_refl; try PSD.fsetdec.

Lemma add_v_le x A s : le_st s (add_v x A s).
Proof. unfold add_v. le_simpl. Qed.

Lemma add_a_le g i A s : le_st s (add_a g i A s).
Proof. unfold add_a. le_simpl; eapply upd_nth_lle. Qed.

Lemma add_f_le z i A s : le_st s (add_f z i A s).
Proof. unfold add_f. le_simpl; eapply upd_nth_lle. Qed.

Lemma add_r_le g A s : le_st s (add_r g A s).
Proof. unfold add_r. le_simpl. Qed.

Lemma add_top_le A s : le_st s (add_top A s).
Proof. unfold add_top. le_simpl. Qed.

Lemma escape_le A s : le_st s (escape A s).
Proof. unfold escape. le_simpl. Qed.

Lemma expose_args_le g n s : le_st s (expose_args g n s).
Proof. unfold expose_args. le_simpl; eapply expose_lle. Qed.

Lemma add_t_le t A s : le_st s (add_t t A s).
Proof. destruct t; [ eapply add_v_le | eapply add_r_le | eapply add_top_le ]. Qed.

Lemma fold_i_le {B} (g : st -> nat -> B -> st) :
  (forall s i b, le_st s (g s i b)) -> forall l i s, le_st s (fold_i g i l s).
Proof.
  intros Hg l. induction l; intros i s; simpl; [ eapply le_refl |].
  eapply le_trans; [ eapply Hg | eapply IHl ].
Qed.

Lemma fold_left_le {B} (g : st -> B -> st) :
  (forall s b, le_st s (g s b)) -> forall l s, le_st s (fold_left g l s).
Proof.
  intros Hg l. induction l; intros s; simpl; [ eapply le_refl |].
  eapply le_trans; [ eapply Hg | eapply IHl ].
Qed.

Lemma ps_fold_le (g : lab -> st -> st) :
  (forall l s, le_st s (g l s)) -> forall A s, le_st s (PS.fold g A s).
Proof.
  intros Hg A s. rewrite PS.fold_spec. eapply fold_left_le. intros; eapply Hg.
Qed.

Lemma use_site_le fn y s : le_st s (fst (use_site fn y s)).
Proof.
  unfold use_site. destruct (_ || _); simpl; [ eapply escape_le | eapply le_refl ].
Qed.

(** Peel the outermost operation of a state *)
Ltac peel T := eapply le_trans; [| T ].

Lemma call_le f ys t s : le_st s (call f ys t s).
Proof.
  unfold call. pose proof (use_site_le true f s) as Hu.
  destruct (use_site true f s) as [s1 ex]. simpl in Hu. cbv beta iota zeta.
  peel ltac:(destruct ex; [ eapply fold_left_le; intros; eapply escape_le | eapply le_refl ]).
  peel ltac:(destruct (PS.mem ltop _); [ eapply add_t_le | eapply le_refl ]).
  peel ltac:(eapply ps_fold_le; intros l s'; destruct l;
             [ eapply le_refl | peel ltac:(eapply add_t_le); eapply fold_i_le; intros; eapply add_a_le
             | eapply le_refl ]).
  exact Hu.
Qed.

(** An induction principle on terms with all branches of a case at once *)
Lemma exp_ind_br (P : term.exp -> Prop) (P0 : term.fundefs -> Prop) :
  (forall x c ys e, P e -> P (term.Econstr x c ys e)) ->
  (forall y cl, Forall (fun p => P (snd p)) cl -> P (term.Ecase y cl)) ->
  (forall x c n y e, P e -> P (term.Eproj x c n y e)) ->
  (forall x f ft ys e, P e -> P (term.Eletapp x f ft ys e)) ->
  (forall B, P0 B -> forall e, P e -> P (term.Efun B e)) ->
  (forall f ft ys, P (term.Eapp f ft ys)) ->
  (forall x p e, P e -> P (term.Eprim_val x p e)) ->
  (forall x p ys e, P e -> P (term.Eprim x p ys e)) ->
  (forall x, P (term.Ehalt x)) ->
  (forall g t xs e, P e -> forall B, P0 B -> P0 (term.Fcons g t xs e B)) ->
  P0 term.Fnil ->
  forall e, P e.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 e.
  enough (He : P e /\ match e with term.Ecase _ cl => Forall (fun p => P (snd p)) cl | _ => True end)
    by apply He.
  revert e. eapply (term.exp_mut
                      (fun e => P e /\ match e with
                                       | term.Ecase _ cl => Forall (fun p => P (snd p)) cl
                                       | _ => True end) P0);
    intros; repeat match goal with H : _ /\ _ |- _ => destruct H end; eauto.
Qed.

Ltac step_fds_body IHb IHB :=
  peel ltac:(eapply IHB); peel ltac:(eapply IHb);
  peel ltac:(eapply fold_i_le; intros; peel ltac:(eapply add_v_le); eapply add_a_le);
  eapply add_v_le.

Lemma step_le : forall e cur s, le_st s (step cur e s).
Proof.
  - eapply (exp_ind_br (fun e => forall cur s, le_st s (step cur e s))
                       (fun B => forall s, le_st s (step_fds B s)));
      intros; simpl.
    + (* constr *)
      match goal with IH : forall cur s, le_st s (step cur ?e s) |- _ => peel ltac:(eapply IH) end.
      peel ltac:(eapply fold_i_le; intros; eapply add_f_le).
      eapply add_v_le.
    + (* case *)
      pose proof (use_site_le false y s) as Hu.
      destruct (use_site false y s) as [s1 b]. simpl in Hu |- *.
      eapply le_trans; [ exact Hu |]. clear Hu. revert s1.
      match goal with H : Forall _ _ |- _ => induction H as [| [c e] cl He Hall IH ] end;
        intros s'; simpl; [ eapply le_refl |].
      eapply le_trans; [ eapply He | eapply IH ].
    + (* proj *)
      match goal with IH : forall cur s, le_st s (step cur ?e s) |- _ => peel ltac:(eapply IH) end.
      peel ltac:(eapply ps_fold_le; intros l s'; destruct l; try eapply le_refl; eapply add_v_le).
      eapply use_site_le.
    + match goal with IH : forall cur s, le_st s (step cur ?e s) |- _ => peel ltac:(eapply IH) end.
      eapply call_le.
    + match goal with IH : forall cur s, le_st s (step cur ?e s) |- _ => peel ltac:(eapply IH) end.
      eauto.
    + eapply call_le.
    + eauto.
    + eauto.
    + eapply add_t_le.
    + (* fundefs *)
      match goal with
      | IHb : forall cur s, le_st s (step cur ?b s), IHB : forall s, le_st s (step_fds ?B s) |- _ =>
          step_fds_body IHb IHB
      end.
    + eapply le_refl.
Qed.

Lemma expose_label_le l s : le_st s (expose_label l s).
Proof.
  destruct l; simpl; [ | | eapply le_refl ].
  - eapply fold_left_le. intros; eapply escape_le.
  - peel ltac:(eapply escape_le). eapply expose_args_le.
Qed.

Lemma round_le e s : le_st s (round e s).
Proof.
  unfold round. peel ltac:(eapply ps_fold_le; intros; eapply expose_label_le).
  peel ltac:(eapply escape_le). eapply step_le.
Qed.

(** * The measure grows with the state and is bounded *)

Lemma NoDup_elements A : NoDup (PS.elements A).
Proof.
  pose proof (PS.elements_spec2w A) as H. induction H; constructor; eauto.
  intros Hin. apply H. eapply In_InA; eauto; typeclasses eauto.
Qed.

Lemma elements_In l A : List.In l (PS.elements A) <-> PS.In l A.
Proof.
  rewrite <- PS.elements_spec1. split; intros H.
  - eapply In_InA; eauto; typeclasses eauto.
  - eapply InA_alt in H as (? & -> & ?); eauto.
Qed.

Lemma cnt_filter U A : cnt U A = length (List.filter (fun l => PS.mem l U) (PS.elements A)).
Proof.
  unfold cnt. rewrite PS.fold_spec.
  assert (Hg : forall l n, fold_left (fun n l => if PS.mem l U then S n else n) l n =
                      n + length (List.filter (fun l => PS.mem l U) l)).
  { induction l as [| a l IH]; intros n; simpl; [ lia |].
    rewrite IH. destruct (PS.mem a U); simpl; lia. }
  rewrite Hg. reflexivity.
Qed.

Lemma cnt_mono U A A' : PS.Subset A A' -> cnt U A <= cnt U A'.
Proof.
  intros Hs. rewrite !cnt_filter. eapply NoDup_incl_length.
  - eapply NoDup_filter, NoDup_elements.
  - intros l Hl. eapply filter_In in Hl as [Hl Hm]. eapply filter_In. split; [| assumption ].
    eapply elements_In. eapply Hs. eapply elements_In. assumption.
Qed.

Lemma cnt_bound U A : cnt U A <= PS.cardinal U.
Proof.
  rewrite cnt_filter, PS.cardinal_spec. eapply NoDup_incl_length.
  - eapply NoDup_filter, NoDup_elements.
  - intros l Hl. eapply filter_In in Hl as [_ Hm]. eapply elements_In, PS.mem_spec. assumption.
Qed.

Lemma cnt_list_mono U N l l' : lle l l' -> cnt_list U N l <= cnt_list U N l'.
Proof.
  intros [Hl Hs]. unfold cnt_list.
  pose proof (sum_mono (fun i => cnt U (nth i l PS.empty)) (fun i => cnt U (nth i l' PS.empty))
                       (seq 0 N) (fun i => cnt_mono U _ _ (Hs i))).
  lia.
Qed.

Lemma cnt_list_bound U N l : cnt_list U N l <= N + N * PS.cardinal U.
Proof.
  unfold cnt_list.
  pose proof (sum_bound (fun i => cnt U (nth i l PS.empty)) (PS.cardinal U) (seq 0 N)
                        (fun i => cnt_bound U _)).
  rewrite length_seq in H. lia.
Qed.

Lemma umeasure_mono Ks U N s s' : le_st s s' -> umeasure Ks U N s <= umeasure Ks U N s'.
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6). unfold umeasure.
  pose proof (sum_mono (A := positive) _ _ Ks (fun k => cnt_mono U _ _ (H1 k))).
  pose proof (sum_mono (A := positive) _ _ Ks (fun k => cnt_list_mono U N _ _ (H2 k))).
  pose proof (sum_mono (A := positive) _ _ Ks (fun k => cnt_list_mono U N _ _ (H3 k))).
  pose proof (sum_mono (A := positive) _ _ Ks (fun k => cnt_mono U _ _ (H4 k))).
  pose proof (cnt_mono U _ _ H5). pose proof (cnt_mono U _ _ H6).
  lia.
Qed.

Definition ubound_nat (nk nu na : nat) : nat :=
  nk * nu + nk * (na + na * nu) + nk * (na + na * nu) + nk * nu + nu + nu.

Lemma umeasure_bound (Ks : list positive) U N s :
  umeasure Ks U N s <= ubound_nat (length Ks) (PS.cardinal U) N.
Proof.
  unfold umeasure, ubound_nat.
  pose proof (sum_bound (A := positive) (fun k => cnt U (gv (st_v s) k)) _ Ks (fun k => cnt_bound U _)).
  pose proof (sum_bound (A := positive) (fun k => cnt_list U N (gl (st_a s) k)) _ Ks (fun k => cnt_list_bound U N _)).
  pose proof (sum_bound (A := positive) (fun k => cnt_list U N (gl (st_f s) k)) _ Ks (fun k => cnt_list_bound U N _)).
  pose proof (sum_bound (A := positive) (fun k => cnt U (gv (st_r s) k)) _ Ks (fun k => cnt_bound U _)).
  pose proof (cnt_bound U (st_top s)). pose proof (cnt_bound U (st_x s)).
  set (a := length Ks * PS.cardinal U) in *.
  set (b := length Ks * (N + N * PS.cardinal U)) in *. lia.
Qed.

Lemma ubound_to_nat nk nu na :
  N.to_nat (ubound (N.of_nat nk) (N.of_nat nu) (N.of_nat na)) = ubound_nat nk nu na.
Proof.
  unfold ubound, ubound_nat.
  repeat (rewrite ?N2Nat.inj_add, ?N2Nat.inj_mul). rewrite !Nat2N.id. reflexivity.
Qed.

Lemma succ_pos_to_nat n : Pos.to_nat (N.succ_pos n) = S (N.to_nat n).
Proof.
  change (Pos.to_nat (N.succ_pos n)) with (N.to_nat (Npos (N.succ_pos n))).
  rewrite N.succ_pos_spec, N2Nat.inj_succ. reflexivity.
Qed.

(** * The solver always reaches a fixpoint *)

Theorem solve_loop_done e : exists s, solve_loop e = Done s.
Proof.
  unfold solve_loop. cbv zeta.
  set (vs := vars_acc e PS.empty). set (Ks := PS.elements vs). set (U := ulabels vs).
  pose proof (umeasure_bound Ks U (arity e)) as Hb.
  pose proof (umeasure_mono Ks U (arity e)) as Hm.
  remember (ubound_nat (length Ks) (PS.cardinal U) (arity e)) as h eqn:Eh.
  eapply loop_done with (mu := fun s => h - umeasure Ks U (arity e) s).
  - intros s Hs. eapply Nat.eqb_neq in Hs.
    specialize (Hm _ _ (round_le e s)). assert (Hb' : umeasure Ks U (arity e) (round e s) <= h) by (rewrite Eh; exact (Hb _)). lia.
  - rewrite succ_pos_to_nat, ubound_to_nat.
    eapply Nat.lt_le_trans with (m := S h); [ lia |]. rewrite Eh. apply le_n.
Qed.

Theorem solve_some e : exists r, solve e = Some r.
Proof.
  unfold solve. destruct (solve_loop_done e) as [s Hs]. rewrite Hs. eauto.
Qed.

(** * Merging internal webs stabilizes *)

Definition mle (iw iw' : M.t positive) : Prop := forall l, (find_w iw' l <= find_w iw l)%positive.

Lemma fold_min_le (g : lab -> positive) L m0 :
  (fold_left (fun m l => Pos.min m (g l)) L m0 <= m0)%positive /\
  forall x, In x L -> (fold_left (fun m l => Pos.min m (g l)) L m0 <= g x)%positive.
Proof.
  revert m0. induction L as [| a L IH]; intros m0; simpl; [ split; [ lia | easy ] |].
  destruct (IH (Pos.min m0 (g a))) as [H1 H2]. split; [ lia |].
  intros x [-> | Hx]; [ lia | eauto ].
Qed.

Lemma find_w_set iw l m x : find_w (M.set l m iw) x = if peq x l then m else find_w iw x.
Proof. unfold find_w, getd. rewrite M.gsspec. destruct (peq x l); reflexivity. Qed.

Lemma fold_set_find K m : forall iw x,
  (In x K /\ find_w (fold_left (fun iw l => M.set l m iw) K iw) x = m) \/
  find_w (fold_left (fun iw l => M.set l m iw) K iw) x = find_w iw x.
Proof.
  induction K as [| a K IH]; intros iw x; simpl; [ eauto |].
  destruct (IH (M.set a m iw) x) as [[Hin Heq] | Heq]; [ left; eauto |].
  rewrite Heq, find_w_set. destruct (peq x a); [ subst; left | right ]; eauto.
Qed.

Lemma merge_site_le s iw site : mle iw (merge_site s iw site).
Proof.
  unfold merge_site. destruct site as [fn y].
  destruct (PS.elements _) as [| l0 K] eqn:HK; intros x; [ lia |].
  destruct (fold_set_find (l0 :: K) (fold_left (fun m l => Pos.min m (find_w iw l)) (l0 :: K) (find_w iw l0)) iw x)
    as [[Hin ->] | ->]; [| lia ].
  eapply fold_min_le. assumption.
Qed.

Lemma merge_pass_le s ss : forall iw, mle iw (fold_left (merge_site s) ss iw).
Proof.
  induction ss as [| site ss IH]; intros iw x; simpl; [ lia |].
  specialize (merge_site_le s iw site x). specialize (IH (merge_site s iw site) x). lia.
Qed.

Lemma forallb_false {A} (p : A -> bool) l : forallb p l = false -> exists x, In x l /\ p x = false.
Proof.
  induction l as [| a l IH]; simpl; [ discriminate |].
  destruct (p a) eqn:Ha; simpl; intros H; [ destruct (IH H) as (x & ? & ?) | ]; eauto.
Qed.

Lemma merge_fuel_to_nat ls : Pos.to_nat (merge_fuel ls) = S (@sum lab Pos.to_nat ls).
Proof.
  unfold merge_fuel. rewrite succ_pos_to_nat. f_equal.
  assert (Hg : forall n0, N.to_nat (fold_left (fun n l => (n + Npos l)%N) ls n0) =
                     N.to_nat n0 + @sum lab Pos.to_nat ls).
  { induction ls as [| a ls IH]; intros n0; simpl; [ lia |].
    rewrite IH, N2Nat.inj_add. simpl. lia. }
  rewrite Hg. reflexivity.
Qed.

Theorem merge_done s ss ls : exists iw, merge_loop s ss ls = Done iw.
Proof.
  unfold merge_loop.
  eapply loop_done with (mu := fun iw => sum (fun l => Pos.to_nat (find_w iw l)) ls).
  - intros iw Hs. eapply sum_strict.
    + intros l. specialize (merge_pass_le s ss iw l). lia.
    + apply forallb_false in Hs as (l & Hl & Hne). exists l. split; [ assumption |].
      specialize (merge_pass_le s ss iw l). apply Pos.eqb_neq in Hne. lia.
  - rewrite merge_fuel_to_nat. cbv beta.
    pose proof (sum_mono (fun l => Pos.to_nat (find_w (M.empty positive) l)) Pos.to_nat ls
                         (fun l => le_n _)). lia.
Qed.
