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

Theorem solve_loop_from_done e s0 : exists s, solve_loop_from e s0 = Done s.
Proof.
  unfold solve_loop_from. cbv zeta.
  set (vs := vars_acc e (identifiers.exp_fv e)). set (Ks := PS.elements vs). set (U := ulabels vs).
  pose proof (umeasure_bound Ks U (arity e)) as Hb.
  pose proof (umeasure_mono Ks U (arity e)) as Hm.
  remember (ubound_nat (length Ks) (PS.cardinal U) (arity e)) as h eqn:Eh.
  eapply loop_done with (mu := fun s => h - umeasure Ks U (arity e) s).
  - intros s Hs. eapply Nat.eqb_neq in Hs.
    specialize (Hm _ _ (round_le e s)). assert (Hb' : umeasure Ks U (arity e) (round e s) <= h) by (rewrite Eh; exact (Hb _)). lia.
  - rewrite succ_pos_to_nat, ubound_to_nat.
    eapply Nat.lt_le_trans with (m := S h); [ lia |]. rewrite Eh. apply le_n.
Qed.

Theorem solve_loop_done e : exists s, solve_loop e = Done s.
Proof. eapply solve_loop_from_done. Qed.

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

(** * The state stays within the universe of the program *)

Definition lab_in (V : PS.t) (l : lab) : Prop :=
  match l with xH => True | xO x | xI x => PS.In x V end.

(** Sets of labels of the universe *)
Definition sok (V : PS.t) (A : PS.t) : Prop := forall l, PS.In l A -> lab_in V l.

(** Lists of sets of the universe, no longer than the largest arity *)
Definition lok (V : PS.t) (N : nat) (l : list PS.t) : Prop :=
  length l <= N /\ forall i, sok V (nth i l PS.empty).

Record inv (V : PS.t) (N : nat) (s : st) : Prop :=
  { iv_v : forall k, sok V (gv (st_v s) k);
    iv_vk : forall k, ~ PS.In k V -> PS.Subset (gv (st_v s) k) PS.empty;
    iv_a : forall k, lok V N (gl (st_a s) k);
    iv_ak : forall k, ~ PS.In k V -> gl (st_a s) k = [];
    iv_f : forall k, lok V N (gl (st_f s) k);
    iv_fk : forall k, ~ PS.In k V -> gl (st_f s) k = [];
    iv_r : forall k, sok V (gv (st_r s) k);
    iv_rk : forall k, ~ PS.In k V -> PS.Subset (gv (st_r s) k) PS.empty;
    iv_top : sok V (st_top s);
    iv_x : sok V (st_x s) }.

Lemma sok_union V A B : sok V A -> sok V B -> sok V (PS.union A B).
Proof. intros HA HB l Hl. apply PS.union_spec in Hl as [Hl | Hl]; eauto. Qed.

Lemma sok_sub V A B : PS.Subset A B -> sok V B -> sok V A.
Proof. intros Hs HB l Hl. eauto. Qed.

Lemma sok_empty V : sok V PS.empty.
Proof. intros l Hl. apply PS.empty_spec in Hl. contradiction. Qed.

Lemma sok_single V l : lab_in V l -> sok V (PS.singleton l).
Proof. intros H l' Hl. apply PS.singleton_spec in Hl. subst. exact H. Qed.

Lemma sok_add_top V A : sok V A -> sok V (PS.add ltop A).
Proof. intros H l Hl. apply PS.add_spec in Hl as [-> | Hl]; [ exact I | eauto ]. Qed.

Lemma sok_remove V l A : sok V A -> sok V (PS.remove l A).
Proof. intros H l' Hl. apply PS.remove_spec in Hl as [Hl _]. eauto. Qed.

Lemma sok_nth V N l i : lok V N l -> sok V (nth i l PS.empty).
Proof. intros [_ H]. eapply H. Qed.

Lemma upd_nth_length l i A : length (upd_nth l i A) = Nat.max (length l) (S i).
Proof.
  revert i. induction l as [| B l IH]; intros i.
  - induction i as [| i IHi]; simpl in *; [ reflexivity | rewrite IHi; reflexivity ].
  - destruct i as [| i]; simpl; [ lia | rewrite IH; lia ].
Qed.

Lemma upd_nth_sub l i A j :
  PS.Subset (nth j (upd_nth l i A) PS.empty) (PS.union (nth j l PS.empty) A).
Proof.
  revert i j. induction l as [| B l IH]; intros i j.
  - revert j. induction i as [| i IHi]; intros j; simpl.
    + destruct j as [| [| j]]; simpl; PSD.fsetdec.
    + destruct j as [| j]; simpl; [ PSD.fsetdec |].
      specialize (IHi j). rewrite nth_nil in *. exact IHi.
  - destruct i as [| i], j as [| j]; simpl; try PSD.fsetdec. eapply IH.
Qed.

Lemma lok_upd V N l i A : lok V N l -> i < N -> sok V A -> lok V N (upd_nth l i A).
Proof.
  intros [Hl Hs] Hi HA. split; [ rewrite upd_nth_length; lia |].
  intros j. eapply sok_sub; [ eapply upd_nth_sub | eapply sok_union; eauto ].
Qed.

Lemma lok_expose V N l n :
  lok V N l -> n <= N -> lok V N (map (PS.add ltop) (l ++ repeat PS.empty (n - length l))).
Proof.
  intros [Hl Hs] Hn. split; [ rewrite length_map, length_app, repeat_length; lia |].
  intros j. destruct (Nat.lt_ge_cases j (length l + (n - length l))) as [Hj | Hj].
  - rewrite (nth_indep (map (PS.add ltop) (l ++ repeat PS.empty (n - length l)))
                       PS.empty (PS.add ltop PS.empty))
      by (rewrite length_map, length_app, repeat_length; lia).
    rewrite map_nth. eapply sok_add_top.
    destruct (Nat.lt_ge_cases j (length l)).
    + rewrite app_nth1 by assumption. eauto.
    + rewrite app_nth2 by assumption. rewrite nth_repeat. eapply sok_empty.
  - rewrite nth_overflow by (rewrite length_map, length_app, repeat_length; lia). eapply sok_empty.
Qed.

Lemma lok_nil V N : lok V N [].
Proof. split; [ simpl; lia | intros i; rewrite nth_nil; eapply sok_empty ]. Qed.

(** ** Operations preserve the invariant *)

Section Ops.

  Variables (V : PS.t) (N : nat).

  Ltac inv_tac :=
    match goal with H : inv _ _ _ |- _ => destruct H end;
    constructor; simpl; intros;
    repeat match goal with
           | |- context [ gv (M.set _ _ _) _ ] => rewrite gv_set
           | |- context [ gl (M.set _ _ _) _ ] => rewrite gl_set
           | |- context [ if peq ?k ?x then _ else _ ] => destruct (peq k x); subst
           end;
    try contradiction; eauto.

  Lemma add_v_inv x A s : inv V N s -> PS.In x V -> sok V A -> inv V N (add_v x A s).
  Proof. intros; unfold add_v; inv_tac. eapply sok_union; eauto. Qed.

  Lemma add_a_inv g i A s : inv V N s -> PS.In g V -> i < N -> sok V A -> inv V N (add_a g i A s).
  Proof. intros; unfold add_a; inv_tac. eapply lok_upd; eauto. Qed.

  Lemma add_f_inv z i A s : inv V N s -> PS.In z V -> i < N -> sok V A -> inv V N (add_f z i A s).
  Proof. intros; unfold add_f; inv_tac. eapply lok_upd; eauto. Qed.

  Lemma add_r_inv g A s : inv V N s -> PS.In g V -> sok V A -> inv V N (add_r g A s).
  Proof. intros; unfold add_r; inv_tac. eapply sok_union; eauto. Qed.

  Lemma add_top_inv A s : inv V N s -> sok V A -> inv V N (add_top A s).
  Proof. intros; unfold add_top; inv_tac. eapply sok_union; eauto. Qed.

  Lemma escape_inv A s : inv V N s -> sok V A -> inv V N (escape A s).
  Proof. intros; unfold escape; inv_tac. eapply sok_union; [| eapply sok_remove ]; eauto. Qed.

  Lemma expose_args_inv g n s : inv V N s -> PS.In g V -> n <= N -> inv V N (expose_args g n s).
  Proof. intros; unfold expose_args; inv_tac. eapply lok_expose; eauto. Qed.

  Definition tgt_in (t : tgt) : Prop :=
    match t with TVar x | TRet x => PS.In x V | TTop => True end.

  Lemma add_t_inv t A s : inv V N s -> tgt_in t -> sok V A -> inv V N (add_t t A s).
  Proof.
    destruct t; simpl; intros; [ eapply add_v_inv | eapply add_r_inv | eapply add_top_inv ]; eauto.
  Qed.

End Ops.

Lemma fold_i_inv {B} (P : st -> Prop) (g : st -> nat -> B -> st) l :
  forall i0, (forall s i b, P s -> List.In b l -> i < i0 + length l -> P (g s i b)) ->
  forall s, P s -> P (fold_i g i0 l s).
Proof.
  induction l as [| a l IH]; intros i0 Hg s Hs; simpl; [ assumption |].
  eapply IH; [| eapply Hg; simpl; eauto; lia ].
  intros s' i b Hs' Hb Hi. eapply Hg; simpl; eauto. lia.
Qed.

Lemma fold_left_inv {B} (P : st -> Prop) (g : st -> B -> st) l :
  (forall s b, P s -> List.In b l -> P (g s b)) -> forall s, P s -> P (fold_left g l s).
Proof.
  induction l as [| a l IH]; intros Hg s Hs; simpl; [ assumption |].
  eapply IH; [ intros; eapply Hg; simpl; eauto | eapply Hg; simpl; eauto ].
Qed.

Lemma ps_fold_inv (P : st -> Prop) (g : lab -> st -> st) A :
  (forall l s, P s -> PS.In l A -> P (g l s)) -> forall s, P s -> P (PS.fold g A s).
Proof.
  intros Hg s Hs. rewrite PS.fold_spec. eapply fold_left_inv; eauto.
  intros s' l Hs' Hl. eapply Hg; eauto. eapply elements_In. assumption.
Qed.

(** ** Terms within the universe *)

Fixpoint uin (V : PS.t) (N : nat) (e : term.exp) : Prop :=
  match e with
  | term.Econstr x _ ys e => PS.In x V /\ Forall (fun y => PS.In y V) ys /\ length ys <= N /\ uin V N e
  | term.Ecase y cl =>
      PS.In y V /\
      (fix uin_br (cl : list (term.ctor_tag * term.exp)) :=
         match cl with
         | [] => True
         | (_, e) :: cl => uin V N e /\ uin_br cl
         end) cl
  | term.Eproj x _ _ y e => PS.In x V /\ PS.In y V /\ uin V N e
  | term.Eletapp x f _ ys e =>
      PS.In x V /\ PS.In f V /\ Forall (fun y => PS.In y V) ys /\ length ys <= N /\ uin V N e
  | term.Efun B e => uin_fds V N B /\ uin V N e
  | term.Eapp f _ ys => PS.In f V /\ Forall (fun y => PS.In y V) ys /\ length ys <= N
  | term.Eprim_val _ _ e | term.Eprim _ _ _ e => uin V N e
  | term.Ehalt x => PS.In x V
  end
with uin_fds (V : PS.t) (N : nat) (B : term.fundefs) : Prop :=
  match B with
  | term.Fcons g _ xs b B =>
      PS.In g V /\ Forall (fun x => PS.In x V) xs /\ length xs <= N /\ uin V N b /\ uin_fds V N B
  | term.Fnil => True
  end.

Lemma Forall_In_mono V V' (l : list var) :
  PS.Subset V V' -> Forall (fun y => PS.In y V) l -> Forall (fun y => PS.In y V') l.
Proof. intros Hs H. eapply Forall_impl; [| exact H ]. intros; eauto. Qed.

Lemma uin_mono V V' N N' (HV : PS.Subset V V') (HN : N <= N') :
  forall e, uin V N e -> uin V' N' e.
Proof.
  eapply (exp_ind_br (fun e => uin V N e -> uin V' N' e) (fun B => uin_fds V N B -> uin_fds V' N' B));
    simpl; intros.
  2:{ destruct H0 as [Hy Hbr]. split; [ eauto |]. revert Hbr.
      induction H as [| [c e] cl He Hall IH ]; simpl in *; [ easy |].
      intros [Hb1 Hb2]. split; [ eauto | exact (IH Hb2) ]. }
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; eauto using Forall_In_mono; try lia.
Qed.

Lemma uin_fds_mono V V' N N' (HV : PS.Subset V V') (HN : N <= N') :
  forall B, uin_fds V N B -> uin_fds V' N' B.
Proof.
  induction B as [g t xs b B IH |]; simpl; [| easy ].
  intros (H1 & H2 & H3 & H4 & H5). repeat split; eauto using Forall_In_mono, uin_mono; lia.
Qed.

Lemma add_list_spec l : forall acc,
  PS.Subset acc (add_list l acc) /\ Forall (fun y => PS.In y (add_list l acc)) l.
Proof.
  unfold add_list. induction l as [| a l IH]; intros acc; simpl; [ split; [ PSD.fsetdec | constructor ] |].
  destruct (IH (PS.add a acc)) as [H1 H2]. split; [ PSD.fsetdec |].
  constructor; [ eapply H1; PSD.fsetdec | exact H2 ].
Qed.

Ltac add_list_facts :=
  repeat match goal with
         | |- context [ add_list ?l ?acc ] =>
             let H1 := fresh "Hal" in let H2 := fresh "Hal" in
             destruct (add_list_spec l acc) as [H1 H2];
             generalize dependent (add_list l acc); intros
         end.

Lemma vars_acc_spec :
  forall e acc, PS.Subset acc (vars_acc e acc) /\ uin (vars_acc e acc) (arity e) e.
Proof.
  eapply (exp_ind_br (fun e => forall acc, PS.Subset acc (vars_acc e acc) /\ uin (vars_acc e acc) (arity e) e)
                     (fun B => forall acc, PS.Subset acc (vars_fds B acc) /\
                                           uin_fds (vars_fds B acc) (arity_fds B) B));
    intros; simpl.
  - (* constr *)
    destruct (add_list_spec (x :: ys) acc) as [Hs Hf]. inv Hf.
    destruct (H (add_list (x :: ys) acc)) as [He Hu].
    split; [ PSD.fsetdec |]. split; [ eauto |]. split; [ eapply Forall_In_mono; eauto |].
    split; [ lia | eapply uin_mono; [ | | eassumption ]; [ PSD.fsetdec | lia ] ].
  - (* case *)
    assert (Hbr : forall a, PS.Subset a ((fix vars_br (cl : list (term.ctor_tag * term.exp)) (acc : PS.t) :=
                                          match cl with
                                          | [] => acc
                                          | (_, e) :: cl => vars_br cl (vars_acc e acc)
                                          end) cl a) /\
                       (fix uin_br (cl0 : list (term.ctor_tag * term.exp)) :=
                          match cl0 with
                          | [] => True
                          | (_, e) :: cl0 => uin ((fix vars_br (cl : list (term.ctor_tag * term.exp)) (acc : PS.t) :=
                                                   match cl with
                                                   | [] => acc
                                                   | (_, e) :: cl => vars_br cl (vars_acc e acc)
                                                   end) cl a)
                                                 ((fix arity_br (cl : list (term.ctor_tag * term.exp)) :=
                                                     match cl with
                                                     | [] => 0
                                                     | (_, e) :: cl => Nat.max (arity e) (arity_br cl)
                                                     end) cl) e /\ uin_br cl0
                          end) cl).
    { match goal with H : Forall _ ?cl |- _ => induction H as [| [c e] cl He Hall IH ] end;
        intros a; simpl; [ split; [ PSD.fsetdec | exact I ] |].
      destruct (He a) as [He1 He2]. destruct (IH (vars_acc e a)) as [IH1 IH2].
      split; [ PSD.fsetdec |]. split.
      - eapply uin_mono; [ | | eassumption ]; [ eassumption | simpl; lia ].
      - (* the remaining branches, with a larger set of variables and arity *)
        clear -IH2 He1 IH1.
        revert IH2. generalize (vars_acc e a). intros a' H'.
        assert (Hgen : forall V N V' N', PS.Subset V V' -> N <= N' ->
                  (fix uin_br (cl0 : list (term.ctor_tag * term.exp)) :=
                     match cl0 with [] => True | (_, e) :: cl0 => uin V N e /\ uin_br cl0 end) cl ->
                  (fix uin_br (cl0 : list (term.ctor_tag * term.exp)) :=
                     match cl0 with [] => True | (_, e) :: cl0 => uin V' N' e /\ uin_br cl0 end) cl).
        { clear. induction cl as [| [c e] cl IH]; simpl; [ easy |].
          intros V N V' N' HV HN [H1 H2]. split; [ eapply uin_mono; eauto | eapply IH; eauto ]. }
        eapply Hgen; [ | | exact H' ]; [ PSD.fsetdec | lia ]. }
    destruct (Hbr (PS.add y acc)) as [H1 H2]. split; [ PSD.fsetdec |]. split; [ PSD.fsetdec | exact H2 ].
  - (* proj *)
    destruct (H (PS.add x (PS.add y acc))) as [He Hu].
    split; [ PSD.fsetdec |]. repeat split; [ PSD.fsetdec | PSD.fsetdec | assumption ].
  - (* letapp *)
    destruct (add_list_spec (x :: f :: ys) acc) as [Hs Hf]. inv Hf. inv H3.
    destruct (H (add_list (x :: f :: ys) acc)) as [He Hu].
    split; [ PSD.fsetdec |]. split; [ eauto |]. split; [ eauto |].
    split; [ eapply Forall_In_mono; eauto |].
    split; [ lia | eapply uin_mono; [ | | eassumption ]; [ PSD.fsetdec | lia ] ].
  - (* fun *)
    destruct (H acc) as [HB1 HB2]. destruct (H0 (vars_fds B acc)) as [He1 He2].
    split; [ PSD.fsetdec |]. split.
    + eapply uin_fds_mono; [ | | eassumption ]; [ eassumption | lia ].
    + eapply uin_mono; [ | | eassumption ]; [ PSD.fsetdec | lia ].
  - (* app *)
    destruct (add_list_spec (f :: ys) acc) as [Hs Hf]. inv Hf.
    split; [ PSD.fsetdec |]. repeat split; eauto.
  - destruct (H (PS.add x acc)) as [H1 H2]. split; [ PSD.fsetdec | exact H2 ].
  - destruct (add_list_spec (x :: ys) acc) as [Hs _]. destruct (H (add_list (x :: ys) acc)) as [H1 H2].
    split; [ intros l Hl; apply H1, Hs, Hl | eapply uin_mono; [ | | exact H2 ]; [ PSD.fsetdec | lia ] ].
  - split; [ PSD.fsetdec | PSD.fsetdec ].
  - (* fcons *)
    destruct (add_list_spec (g :: xs) acc) as [Hs Hf]. inv Hf.
    destruct (H (add_list (g :: xs) acc)) as [Hb1 Hb2].
    destruct (H0 (vars_acc e (add_list (g :: xs) acc))) as [HB1 HB2].
    split; [ PSD.fsetdec |]. split; [ eauto |]. split; [ eapply Forall_In_mono; [| eauto ]; PSD.fsetdec |].
    split; [ lia |]. split.
    + eapply uin_mono; [ | | eassumption ]; [ PSD.fsetdec | lia ].
    + eapply uin_fds_mono; [ | | eassumption ]; [ PSD.fsetdec | lia ].
  - split; [ PSD.fsetdec | exact I ].
Qed.

(** ** The solver preserves the invariant *)

Lemma lt_len {A} (l : list A) i N : i < 0 + length l -> length l <= N -> i < N.
Proof. intros; lia. Qed.

Section StepInv.

  Variables (V : PS.t) (N : nat).

  Lemma kind_labels_sub fn A : PS.Subset (kind_labels fn A) A.
  Proof.
    intros l Hl. unfold kind_labels in Hl. apply PS.filter_spec in Hl as [Hl _]; [ exact Hl |].
    intros ? ? ->. reflexivity.
  Qed.

  Lemma use_site_inv fn y s : inv V N s -> inv V N (fst (use_site fn y s)).
  Proof.
    intros Hs. unfold use_site. destruct (_ || _); simpl; [| exact Hs ].
    eapply escape_inv; [ exact Hs |]. eapply sok_sub; [ eapply kind_labels_sub | eapply iv_v; eauto ].
  Qed.

  Lemma lab_in_xO g : lab_in V (xO g) -> PS.In g V.
  Proof. exact (fun H => H). Qed.

  Lemma call_inv f ys t s :
    inv V N s -> Forall (fun y => PS.In y V) ys -> length ys <= N -> tgt_in V t ->
    inv V N (call f ys t s).
  Proof.
    intros Hs Hys Hn Ht. unfold call.
    pose proof (use_site_inv true f s Hs) as Hs1.
    pose proof (iv_v _ _ _ Hs f) as HA.
    destruct (use_site true f s) as [s1 ex]. simpl in Hs1. cbv beta iota zeta.
    destruct ex;
      [ eapply fold_left_inv; [ intros; eapply escape_inv; [ eassumption | eapply iv_v; eassumption ] | ] | ];
      (destruct (PS.mem ltop _); [ eapply add_t_inv; [ | exact Ht | eapply sok_single; exact I ] | ]);
      (eapply ps_fold_inv; [| exact Hs1 ]);
      intros l s' Hs' Hl; destruct l as [| g |]; try exact Hs';
      specialize (HA _ Hl); simpl in HA;
      (eapply add_t_inv; [ | exact Ht | eapply iv_r ]);
      try (eapply fold_i_inv; [| exact Hs' ]; intros s'' i y Hs'' Hy Hi;
           eapply add_a_inv; eauto; [ eapply lt_len; eauto | eapply iv_v; eauto ]).
  Qed.

  Lemma step_inv : forall e cur s, uin V N e -> tgt_in V cur -> inv V N s -> inv V N (step cur e s).
  Proof.
    eapply (exp_ind_br (fun e => forall cur s, uin V N e -> tgt_in V cur -> inv V N s -> inv V N (step cur e s))
                       (fun B => forall s, uin_fds V N B -> inv V N s -> inv V N (step_fds B s)));
      intros; simpl in *;
      repeat match goal with H : _ /\ _ |- _ => destruct H end.
    - (* constr *)
      eapply H; eauto. eapply fold_i_inv.
      + intros s' i y Hs' Hy Hi. eapply add_f_inv; eauto; [ eapply lt_len; eauto | eapply iv_v; eauto ].
      + eapply add_v_inv; eauto. eapply sok_single. assumption.
    - (* case *)
      pose proof (use_site_inv false y s H2) as Hs1.
      destruct (use_site false y s) as [s1 b]. simpl in Hs1 |- *.
      revert s1 Hs1 H3.
      induction H as [| [c e] cl He Hall IH ]; intros s1 Hs1 Hbr; simpl in *; [ exact Hs1 |].
      destruct Hbr as [Hb1 Hb2]. eapply IH; eauto.
    - (* proj *)
      eapply H; eauto. pose proof (use_site_inv false y s H2) as Hs1.
      pose proof (iv_v _ _ _ Hs1 y) as HA.
      eapply ps_fold_inv; [| exact Hs1 ]. intros l s' Hs' Hl.
      destruct l; try exact Hs'.
      + eapply add_v_inv; eauto. eapply sok_nth, iv_f; eauto.
      + eapply add_v_inv; eauto. eapply sok_single. exact I.
    - (* letapp *) eapply H; eauto. eapply call_inv; eauto.
    - (* fun *) eapply H0; eauto.
    - (* app *) eapply call_inv; eauto.
    - eauto.
    - eauto.
    - (* halt *) eapply add_t_inv; eauto. eapply iv_v; eauto.
    - (* fundefs *)
      eapply H0; [ assumption | ]. eapply H; [ assumption | assumption | ].
      eapply fold_i_inv.
      + intros s' i x Hs' Hx Hi. eapply add_v_inv.
        * eapply add_a_inv; eauto; [ eapply lt_len; eauto | eapply sok_empty ].
        * eapply Forall_forall in H3; eauto.
        * eapply sok_nth, iv_a. exact Hs'.
      + eapply add_v_inv; eauto. eapply sok_single. assumption.
    - assumption.
  Qed.

  Lemma expose_label_inv l s : inv V N s -> lab_in V l -> inv V N (expose_label l s).
  Proof.
    intros Hs Hl. destruct l; simpl in *.
    - eapply fold_left_inv; [| exact Hs ]. intros s' A Hs' HA.
      eapply escape_inv; eauto. eapply In_nth with (d := PS.empty) in HA as (i & _ & <-).
      eapply sok_nth, iv_f; eauto.
    - eapply escape_inv; [| eapply iv_r; exact Hs ].
      eapply expose_args_inv; [ exact Hs | exact Hl | exact (proj1 (iv_a _ _ _ Hs _)) ].
    - exact Hs.
  Qed.

  Lemma round_inv e s : uin V N e -> inv V N s -> inv V N (round e s).
  Proof.
    intros He Hs. unfold round.
    pose proof (step_inv e TTop s He I Hs) as Hs1.
    pose proof (escape_inv _ _ _ _ Hs1 (iv_top _ _ _ Hs1)) as Hs2.
    revert Hs2. generalize (escape (st_top (step TTop e s)) (step TTop e s)). intros s2 Hs2.
    eapply ps_fold_inv; [| exact Hs2 ]. intros l s' Hs' Hl. eapply expose_label_inv; eauto.
    eapply (iv_x _ _ _ Hs2). exact Hl.
  Qed.

End StepInv.

Lemma init_from_inv e s :
  inv (vars_acc e (identifiers.exp_fv e)) (arity e) s ->
  inv (vars_acc e (identifiers.exp_fv e)) (arity e) (init_from s e).
Proof.
  intros Hs. unfold init_from. destruct (vars_acc_spec e (identifiers.exp_fv e)) as [Hfv _].
  eapply fold_left_inv; [| exact Hs ].
  intros s' x Hs' Hx. eapply add_v_inv; eauto; [| eapply sok_single; exact I ].
  eapply Hfv, elements_In. exact Hx.
Qed.

Lemma empty_inv V N : inv V N empty_st.
Proof.
  constructor; intros; simpl;
    try (unfold gv, gl, getd; rewrite M.gempty);
    try (eapply sok_empty || eapply lok_nil || PSD.fsetdec || reflexivity).
Qed.

Lemma init_inv e : inv (vars_acc e (identifiers.exp_fv e)) (arity e) (init e).
Proof. eapply init_from_inv, empty_inv. Qed.

(** * An unchanged measure means a fixpoint *)

Lemma sum_eq_each {A} (f g : A -> nat) l :
  (forall a, f a <= g a) -> sum f l = sum g l -> forall a, List.In a l -> f a = g a.
Proof.
  intros H. induction l as [| b l IH]; simpl; [ easy |]. intros Heq a [-> | Ha].
  - pose proof (sum_mono f g l H). specialize (H a). lia.
  - pose proof (sum_mono f g l H). specialize (H b). eapply IH; eauto. lia.
Qed.

Lemma ulabels_complete V l : lab_in V l -> PS.In l (ulabels V).
Proof.
  unfold ulabels. rewrite PS.fold_spec.
  assert (Hg : forall xs U0, (PS.In l U0 \/ exists x, List.In x xs /\ (l = lfun x \/ l = lcon x)) ->
                        PS.In l (fold_left (fun U x => PS.add (lfun x) (PS.add (lcon x) U)) xs U0)).
  { induction xs as [| a xs IH]; intros U0 [H | (x & Hx & Hl)]; simpl; eauto; try easy.
    - eapply IH. left. PSD.fsetdec.
    - destruct Hx as [-> | Hx]; eapply IH; [ left; destruct Hl as [-> | ->]; PSD.fsetdec | eauto ]. }
  intros Hl. eapply Hg. destruct l as [x | x |]; simpl in Hl.
  - right. exists x. split; [ eapply elements_In; exact Hl | right; reflexivity ].
  - right. exists x. split; [ eapply elements_In; exact Hl | left; reflexivity ].
  - left. apply PS.singleton_spec. reflexivity.
Qed.

Lemma cnt_eq_sub U A A' :
  PS.Subset A A' -> (forall l, PS.In l A' -> PS.In l U) -> cnt U A = cnt U A' -> PS.Subset A' A.
Proof.
  intros Hs HU Heq l Hl. rewrite !cnt_filter in Heq.
  assert (Hincl : incl (List.filter (fun l => PS.mem l U) (PS.elements A))
                       (List.filter (fun l => PS.mem l U) (PS.elements A'))).
  { intros l' Hl'. eapply filter_In in Hl' as [Hl' Hm]. eapply filter_In. split; [| exact Hm ].
    eapply elements_In, Hs, elements_In. exact Hl'. }
  eapply NoDup_length_incl in Hincl; [| eapply NoDup_filter, NoDup_elements | lia ].
  assert (Hin : List.In l (List.filter (fun l => PS.mem l U) (PS.elements A'))).
  { eapply filter_In. split; [ eapply elements_In; exact Hl | eapply PS.mem_spec; eauto ]. }
  eapply Hincl in Hin. eapply filter_In in Hin as [Hin _]. eapply elements_In. exact Hin.
Qed.

Lemma cnt_list_eq V N l l' :
  lle l l' -> lok V N l' -> cnt_list (ulabels V) N l = cnt_list (ulabels V) N l' -> lle l' l.
Proof.
  intros [Hl Hs] [Hl' Hs'] Heq. unfold cnt_list in Heq.
  pose proof (sum_mono (fun i => cnt (ulabels V) (nth i l PS.empty))
                       (fun i => cnt (ulabels V) (nth i l' PS.empty)) (seq 0 N)
                       (fun i => cnt_mono _ _ _ (Hs i))) as Hsum.
  assert (Hmin : Nat.min (length l) N <= Nat.min (length l') N) by lia.
  split; [ lia |]. intros i. destruct (Nat.lt_ge_cases i N) as [Hi | Hi].
  - eapply cnt_eq_sub; [ eapply Hs | intros l0 H; eapply ulabels_complete; eapply Hs'; exact H |].
    eapply (sum_eq_each (fun i => cnt (ulabels V) (nth i l PS.empty))
                        (fun i => cnt (ulabels V) (nth i l' PS.empty)) (seq 0 N)
                        (fun i => cnt_mono _ _ _ (Hs i))); [ lia |].
    eapply in_seq. lia.
  - rewrite (nth_overflow l') by lia. PSD.fsetdec.
Qed.

Lemma fix_le V N s s' :
  inv V N s' -> le_st s s' ->
  umeasure (PS.elements V) (ulabels V) N s = umeasure (PS.elements V) (ulabels V) N s' ->
  le_st s' s.
Proof.
  intros Hi Hle Heq. pose proof Hle as (H1 & H2 & H3 & H4 & H5 & H6). unfold umeasure in Heq.
  set (U := ulabels V) in *. set (Ks := PS.elements V) in *.
  pose proof (sum_mono (A := positive) _ _ Ks (fun k => cnt_mono U _ _ (H1 k))).
  pose proof (sum_mono (A := positive) _ _ Ks (fun k => cnt_list_mono U N _ _ (H2 k))).
  pose proof (sum_mono (A := positive) _ _ Ks (fun k => cnt_list_mono U N _ _ (H3 k))).
  pose proof (sum_mono (A := positive) _ _ Ks (fun k => cnt_mono U _ _ (H4 k))).
  pose proof (cnt_mono U _ _ H5). pose proof (cnt_mono U _ _ H6).
  assert (HU : forall A, sok V A -> forall l, PS.In l A -> PS.In l U)
    by (intros A HA l Hl; eapply ulabels_complete; eauto).
  assert (Hnil : forall l, lle [] l) by (intros l; split; [ simpl; lia | intros i; rewrite nth_nil; PSD.fsetdec ]).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - intros k. destruct (PSP.In_dec k V) as [Hk | Hk]; [| specialize (iv_vk _ _ _ Hi k Hk); PSD.fsetdec ].
    eapply cnt_eq_sub; [ eapply H1 | eapply HU, iv_v; eauto |].
    eapply (sum_eq_each (A := positive) _ _ Ks (fun k => cnt_mono U _ _ (H1 k))); [ lia |].
    eapply elements_In. exact Hk.
  - intros k. destruct (PSP.In_dec k V) as [Hk | Hk]; [| rewrite (iv_ak _ _ _ Hi k Hk); eapply Hnil ].
    eapply cnt_list_eq; [ eapply H2 | eapply iv_a; eauto |].
    eapply (sum_eq_each (A := positive) _ _ Ks (fun k => cnt_list_mono U N _ _ (H2 k))); [ lia |].
    eapply elements_In. exact Hk.
  - intros k. destruct (PSP.In_dec k V) as [Hk | Hk]; [| rewrite (iv_fk _ _ _ Hi k Hk); eapply Hnil ].
    eapply cnt_list_eq; [ eapply H3 | eapply iv_f; eauto |].
    eapply (sum_eq_each (A := positive) _ _ Ks (fun k => cnt_list_mono U N _ _ (H3 k))); [ lia |].
    eapply elements_In. exact Hk.
  - intros k. destruct (PSP.In_dec k V) as [Hk | Hk]; [| specialize (iv_rk _ _ _ Hi k Hk); PSD.fsetdec ].
    eapply cnt_eq_sub; [ eapply H4 | eapply HU, iv_r; eauto |].
    eapply (sum_eq_each (A := positive) _ _ Ks (fun k => cnt_mono U _ _ (H4 k))); [ lia |].
    eapply elements_In. exact Hk.
  - eapply cnt_eq_sub; [ eapply H5 | eapply HU, iv_top; eauto | lia ].
  - eapply cnt_eq_sub; [ eapply H6 | eapply HU, iv_x; eauto | lia ].
Qed.

(** ** Loops with an invariant *)

Section LoopInv.

  Context {A : Type} (f : A -> A) (stop : A -> A -> bool) (P : A -> Prop).
  Hypothesis (HP : forall a, P a -> P (f a)).

  Lemma loop_more_inv p : forall a a', P a -> loop f stop p a = More a' -> P a'.
  Proof.
    induction p; intros a a' Ha H; simpl in H; unfold loop1 in *.
    - destruct (stop a (f a)); simpl in H; [ discriminate |].
      destruct (loop f stop p (f a)) eqn:H1; simpl in H; [ discriminate |]. eauto.
    - destruct (loop f stop p a) eqn:H1; simpl in H; [ discriminate |]. eauto.
    - destruct (stop a (f a)); inv H. eauto.
  Qed.

  Lemma loop_done_inv p : forall a a', P a -> loop f stop p a = Done a' ->
    exists a0, P a0 /\ a' = f a0 /\ stop a0 a' = true.
  Proof.
    induction p; intros a a' Ha H; simpl in H; unfold loop1 in *.
    - destruct (stop a (f a)) eqn:Hs; simpl in H; [ inv H; eauto |].
      destruct (loop f stop p (f a)) eqn:H1; simpl in H; [ inv H; eauto |].
      eapply IHp; [| exact H ]. eapply loop_more_inv; [| exact H1 ]. eauto.
    - destruct (loop f stop p a) eqn:H1; simpl in H; [ inv H; eauto |].
      eapply IHp; [| exact H ]. eapply loop_more_inv; eauto.
    - destruct (stop a (f a)) eqn:Hs; inv H. eauto.
  Qed.

End LoopInv.

(** The final state of the solver is a fixpoint of a round, reached from the
    initial state. *)
Theorem solve_loop_from_fix e s0 S :
  inv (vars_acc e (identifiers.exp_fv e)) (arity e) s0 ->
  solve_loop_from e s0 = Done S ->
  exists s, le_st s0 s /\ le_st s S /\ le_st S s /\ S = round e s.
Proof.
  unfold solve_loop_from. cbv zeta. intros Hi0 H.
  set (V := vars_acc e (identifiers.exp_fv e)) in *.
  destruct (vars_acc_spec e (identifiers.exp_fv e)) as [_ He]. fold V in He.
  eapply loop_done_inv with (P := fun s => inv V (arity e) s /\ le_st s0 s) in H.
  - destruct H as (s & [Hi Hl] & -> & Hs). eapply Nat.eqb_eq in Hs.
    exists s. split; [ exact Hl | split; [ eapply round_le | ] ]. split; [| reflexivity ].
    eapply fix_le; [ eapply round_inv; eauto | eapply round_le | symmetry; exact Hs ].
  - intros s [Hi Hl]. split; [ eapply round_inv; eauto | eapply le_trans; [ exact Hl | eapply round_le ] ].
  - split; [ exact Hi0 | eapply le_refl ].
Qed.

Theorem solve_loop_fix e S :
  solve_loop e = Done S ->
  exists s0, le_st (init e) s0 /\ le_st s0 S /\ le_st S s0 /\ S = round e s0.
Proof. intros H. eapply solve_loop_from_fix; [ eapply init_inv | exact H ]. Qed.

(** * The constraints satisfied by a fixpoint *)

Definition kind (fn : bool) (l : lab) : bool := if fn then is_flab l else is_clab l.

Lemma kind_labels_spec fn A l : PS.In l (kind_labels fn A) <-> PS.In l A /\ kind fn l = true.
Proof.
  unfold kind_labels. rewrite PS.filter_spec; [| intros ? ? ->; reflexivity ].
  destruct fn; reflexivity.
Qed.

Lemma kind_not_top fn l : kind fn l = true -> l <> ltop.
Proof. unfold ltop. destruct fn, l; simpl; congruence. Qed.

(** ** Facts from a state between [S] and [S] *)

Section Mid.

  Variable (S : st).

  Definition vS x := gv (st_v S) x.
  Definition XS := st_x S.

  Definition tgtS (t : tgt) : PS.t :=
    match t with TVar x => gv (st_v S) x | TRet g => gv (st_r S) g | TTop => st_top S end.

  Definition escS (A : PS.t) : Prop := forall l, PS.In l A -> l = ltop \/ PS.In l XS.

  Lemma upd_nth_at l i A : PS.Subset A (nth i (upd_nth l i A) PS.empty) /\ i < length (upd_nth l i A).
  Proof.
    rewrite upd_nth_length. split; [| lia ]. revert i. induction l as [| B l IH]; intros i.
    - induction i as [| i IHi]; simpl; [ PSD.fsetdec | exact IHi ].
    - destruct i; simpl; [ PSD.fsetdec | eapply IH ].
  Qed.

  Lemma add_v_C x A s : le_st (add_v x A s) S -> PS.Subset A (vS x).
  Proof.
    intros (H & _). specialize (H x). unfold add_v in H. simpl in H. rewrite gv_set in H.
    destruct (peq x x); [| congruence ]. unfold vS. PSD.fsetdec.
  Qed.

  Lemma add_a_C g i A s :
    le_st (add_a g i A s) S -> PS.Subset A (nth i (gl (st_a S) g) PS.empty) /\ i < length (gl (st_a S) g).
  Proof.
    intros (_ & H & _). destruct (H g) as [Hl Hs]. unfold add_a in *. simpl in *.
    rewrite gl_set in Hl, Hs. destruct (peq g g); [| congruence ].
    destruct (upd_nth_at (gl (st_a s) g) i A) as [H1 H2]. specialize (Hs i). split; [ PSD.fsetdec | lia ].
  Qed.

  Lemma add_f_C z i A s :
    le_st (add_f z i A s) S -> PS.Subset A (nth i (gl (st_f S) z) PS.empty).
  Proof.
    intros (_ & _ & H & _). destruct (H z) as [Hl Hs]. unfold add_f in *. simpl in *.
    rewrite gl_set in Hs. destruct (peq z z); [| congruence ].
    destruct (upd_nth_at (gl (st_f s) z) i A) as [H1 H2]. specialize (Hs i). PSD.fsetdec.
  Qed.

  Lemma add_t_C t A s : le_st (add_t t A s) S -> PS.Subset A (tgtS t).
  Proof.
    destruct t; simpl.
    - eapply add_v_C.
    - intros (_ & _ & _ & H & _). specialize (H g). unfold add_r in H. simpl in H. rewrite gv_set in H.
      destruct (peq g g); [| congruence ]. PSD.fsetdec.
    - intros (_ & _ & _ & _ & H & _). unfold add_top in H. simpl in H. PSD.fsetdec.
  Qed.

  Lemma escape_C A s : le_st (escape A s) S -> escS A.
  Proof.
    intros (_ & _ & _ & _ & _ & H) l Hl. unfold escape in H. simpl in H.
    destruct (peq l ltop); [ left; assumption | right ].
    eapply H. eapply PS.union_spec. right. eapply PS.remove_spec. split; [ exact Hl | exact n ].
  Qed.

  Lemma expose_args_C g n s :
    le_st (expose_args g n s) S -> forall i, i < length (gl (st_a s) g) -> PS.In ltop (nth i (gl (st_a S) g) PS.empty).
  Proof.
    intros (_ & H & _) i Hi. destruct (H g) as [_ Hs]. specialize (Hs i). unfold expose_args in Hs. simpl in Hs.
    rewrite gl_set in Hs. destruct (peq g g); [| congruence ]. eapply Hs.
    rewrite (nth_indep _ PS.empty (PS.add ltop PS.empty)) by (rewrite length_map, length_app; lia).
    rewrite map_nth. PSD.fsetdec.
  Qed.

  (** The intermediate states of a fold *)

  Lemma fold_i_mid {B} (g : st -> nat -> B -> st) (Hg : forall s i b, le_st s (g s i b)) l :
    forall i0 s j b, nth_error l j = Some b ->
    exists s', le_st s s' /\ le_st (g s' (i0 + j) b) (fold_i g i0 l s).
  Proof.
    induction l as [| a l IH]; intros i0 s j b Hj; [ destruct j; discriminate |].
    destruct j as [| j]; simpl in *.
    - inv Hj. exists s. split; [ eapply le_refl |]. rewrite Nat.add_0_r. eapply fold_i_le; eauto.
    - destruct (IH (Nat.succ i0) (g s i0 a) j b Hj) as (s' & H1 & H2). exists s'.
      split; [ eapply le_trans; [ eapply Hg | exact H1 ] |]. rewrite <- Nat.add_succ_comm. exact H2.
  Qed.

  Lemma fold_left_mid {B} (g : st -> B -> st) (Hg : forall s b, le_st s (g s b)) l :
    forall s b, List.In b l -> exists s', le_st s s' /\ le_st (g s' b) (fold_left g l s).
  Proof.
    induction l as [| a l IH]; intros s b Hb; [ easy |]. simpl.
    destruct Hb as [-> | Hb].
    - exists s. split; [ eapply le_refl | eapply fold_left_le; eauto ].
    - destruct (IH (g s a) b Hb) as (s' & H1 & H2). exists s'.
      split; [ eapply le_trans; [ eapply Hg | exact H1 ] | exact H2 ].
  Qed.

  Lemma ps_fold_mid (g : lab -> st -> st) (Hg : forall l s, le_st s (g l s)) A s l :
    PS.In l A -> exists s', le_st s s' /\ le_st (g l s') (PS.fold g A s).
  Proof.
    intros Hl. rewrite PS.fold_spec. eapply elements_In in Hl.
    eapply (fold_left_mid (fun s l => g l s)); eauto.
  Qed.

  (** ** Use sites *)

  Definition use_cl (fn : bool) (y : var) : Prop :=
    (PS.In ltop (vS y) \/ exists l, PS.In l (vS y) /\ kind fn l = true /\ PS.In l XS) ->
    forall l, PS.In l (vS y) -> kind fn l = true -> PS.In l XS.

  Lemma use_site_ex fn y s s1 ex :
    le_st S s -> use_site fn y s = (s1, ex) ->
    (PS.In ltop (vS y) \/ exists l, PS.In l (vS y) /\ kind fn l = true /\ PS.In l XS) ->
    ex = true /\ s1 = escape (kind_labels fn (gv (st_v s) y)) s.
  Proof.
    intros (Hv & _ & _ & _ & _ & Hx) Hu Hc. unfold use_site in Hu.
    destruct (PS.mem ltop (gv (st_v s) y) || negb (PS.is_empty (PS.inter (kind_labels fn (gv (st_v s) y)) (st_x s)))) eqn:Hb;
      inv Hu; [ split; reflexivity |].
    exfalso. eapply orb_false_iff in Hb as [Hb1 Hb2]. eapply negb_false_iff, PS.is_empty_spec in Hb2.
    destruct Hc as [Hc | (l & Hl & Hk & Hlx)].
    - eapply Hv in Hc. eapply PS.mem_spec in Hc. congruence.
    - eapply (Hb2 l). eapply PS.inter_spec. split; [ eapply kind_labels_spec; split; [ eapply Hv; exact Hl | exact Hk ] | eapply Hx; exact Hlx ].
  Qed.

  Lemma use_site_C fn y s :
    le_st S s -> le_st (fst (use_site fn y s)) S -> use_cl fn y.
  Proof.
    intros H1 H2 Hc l Hl Hk. destruct (use_site fn y s) as [s1 ex] eqn:Hu.
    destruct (use_site_ex fn y s s1 ex H1 Hu Hc) as [_ Heq]. subst s1. simpl in H2. eapply escape_C in H2.
    assert (HK : PS.In l (kind_labels fn (gv (st_v s) y))).
    { eapply kind_labels_spec. split; [ eapply (proj1 H1); exact Hl | exact Hk ]. }
    destruct (H2 l HK) as [Ht | Hx]; [ eapply kind_not_top in Hk; congruence | exact Hx ].
  Qed.

  (** ** Calls *)

  Definition call_cl (f : var) (ys : list var) (t : tgt) : Prop :=
    use_cl true f /\
    (forall g, PS.In (xO g) (vS f) ->
               (forall i y, nth_error ys i = Some y -> PS.Subset (vS y) (nth i (gl (st_a S) g) PS.empty)) /\
               PS.Subset (gv (st_r S) g) (tgtS t)) /\
    (PS.In ltop (vS f) -> PS.In ltop (tgtS t)) /\
    ((PS.In ltop (vS f) \/ exists g, PS.In (xO g) (vS f) /\ PS.In (xO g) XS) ->
     forall y, List.In y ys -> escS (vS y)).

  Lemma call_C f ys t s :
    le_st S s -> le_st (call f ys t s) S -> call_cl f ys t.
  Proof.
    intros H0 Hc. pose proof (call_le f ys t s) as Hle. unfold call in *.
    pose proof (use_site_le true f s) as Hu1.
    destruct (use_site true f s) as [s1 ex] eqn:Hu. simpl in Hu1. cbv beta iota zeta in Hc.
    set (G := fun l s => match l with
                         | xO g => let s := fold_i (fun s i y => add_a g i (gv (st_v s) y) s) 0 ys s in
                                   add_t t (gv (st_r s) g) s
                         | _ => s
                         end) in Hc.
    assert (HG : forall l s, le_st s (G l s)).
    { intros l s'. destruct l; try eapply le_refl. unfold G. cbv zeta.
      peel ltac:(eapply add_t_le). eapply fold_i_le. intros; eapply add_a_le. }
    set (s2 := PS.fold G (gv (st_v s) f) s1) in Hc.
    set (s3 := if PS.mem ltop (gv (st_v s) f) then add_t t (PS.singleton ltop) s2 else s2) in Hc.
    assert (H23 : le_st s2 s3) by (unfold s3; destruct (PS.mem _ _); [ eapply add_t_le | eapply le_refl ]).
    assert (H3c : le_st s3 S).
    { eapply le_trans; [| exact Hc ]. destruct ex; [ eapply fold_left_le; intros; eapply escape_le | eapply le_refl ]. }
    assert (H2c : le_st s2 S) by (eapply le_trans; eauto).
    assert (H1c : le_st s1 S) by (eapply le_trans; [ eapply ps_fold_le; exact HG | exact H2c ]).
    assert (HS1 : le_st S s1) by (eapply le_trans; eauto).
    assert (Hvf : PS.Subset (vS f) (gv (st_v s) f)) by eapply (proj1 H0).
    split; [| split; [| split ] ].
    - eapply use_site_C with (s := s); [ exact H0 | rewrite Hu; exact H1c ].
    - intros g Hg. eapply Hvf in Hg.
      destruct (ps_fold_mid G HG (gv (st_v s) f) s1 (xO g) Hg) as (sg & Hsg1 & Hsg2).
      fold s2 in Hsg2. unfold G in Hsg2. cbv zeta in Hsg2.
      assert (HgS : le_st (add_t t (gv (st_r (fold_i (fun s i y => add_a g i (gv (st_v s) y) s) 0 ys sg)) g)
                                 (fold_i (fun s i y => add_a g i (gv (st_v s) y) s) 0 ys sg)) S)
        by (eapply le_trans; eauto).
      split.
      + intros i y Hy.
        destruct (fold_i_mid (fun s i y => add_a g i (gv (st_v s) y) s) (fun _ _ _ => add_a_le _ _ _ _) ys 0 sg i y Hy)
          as (sb & Hsb1 & Hsb2).
        simpl in Hsb2. edestruct add_a_C as [Hsub _].
        { eapply le_trans; [ exact Hsb2 | eapply le_trans; [ eapply add_t_le | exact HgS ] ]. }
        assert (HSsb : le_st S sb) by (eapply le_trans; [ exact HS1 | eapply le_trans; eauto ]).
        intros l Hl. eapply Hsub. eapply (proj1 HSsb). exact Hl.
      + eapply add_t_C in HgS. intros l Hl. eapply HgS.
        assert (HSm : le_st S (fold_i (fun s i y => add_a g i (gv (st_v s) y) s) 0 ys sg)).
        { eapply le_trans; [ exact HS1 | eapply le_trans; [ exact Hsg1 | eapply fold_i_le; intros; eapply add_a_le ] ]. }
        eapply (proj1 (proj2 (proj2 (proj2 HSm)))). exact Hl.
    - intros Ht. eapply Hvf, PS.mem_spec in Ht. unfold s3 in H3c. rewrite Ht in H3c.
      eapply add_t_C in H3c. eapply H3c. PSD.fsetdec.
    - intros Hcnd y Hy.
      destruct (use_site_ex true f s s1 ex H0 Hu) as [Hex _].
      { destruct Hcnd as [Ht | (g & Hg & Hgx)]; [ left; exact Ht | right; exists (xO g); eauto ]. }
      subst ex.
      destruct (fold_left_mid (fun s y => escape (gv (st_v s) y) s) (fun _ _ => escape_le _ _) ys s3 y Hy)
        as (sy & Hsy1 & Hsy2).
      assert (HSsy : le_st S sy) by (eapply le_trans; [ exact HS1 | eapply le_trans; [ eapply ps_fold_le; exact HG | eapply le_trans; [ exact H23 | exact Hsy1 ] ] ]).
      intros l Hl. eapply (escape_C _ sy); [ eapply le_trans; [ exact Hsy2 | exact Hc ] |].
      eapply (proj1 HSsy). exact Hl.
  Qed.

  Lemma le_v s s' : le_st s s' -> forall k, PS.Subset (gv (st_v s) k) (gv (st_v s') k).
  Proof. intros H; apply H. Qed.
  Lemma le_a s s' : le_st s s' -> forall k i, PS.Subset (nth i (gl (st_a s) k) PS.empty) (nth i (gl (st_a s') k) PS.empty).
  Proof. intros H k; apply H. Qed.
  Lemma le_a_len s s' : le_st s s' -> forall k, length (gl (st_a s) k) <= length (gl (st_a s') k).
  Proof. intros H k; apply H. Qed.
  Lemma le_f s s' : le_st s s' -> forall k i, PS.Subset (nth i (gl (st_f s) k) PS.empty) (nth i (gl (st_f s') k) PS.empty).
  Proof. intros H k; apply H. Qed.
  Lemma le_f_len s s' : le_st s s' -> forall k, length (gl (st_f s) k) <= length (gl (st_f s') k).
  Proof. intros H k; apply H. Qed.
  Lemma le_r s s' : le_st s s' -> forall k, PS.Subset (gv (st_r s) k) (gv (st_r s') k).
  Proof. intros H; apply H. Qed.
  Lemma le_top s s' : le_st s s' -> PS.Subset (st_top s) (st_top s').
  Proof. intros H; apply H. Qed.
  Lemma le_x s s' : le_st s s' -> PS.Subset (st_x s) (st_x s').
  Proof. intros H; apply H. Qed.

End Mid.

Lemma step_fds_le B s : le_st s (step_fds B s).
Proof.
  revert s. induction B as [g t xs b B IH |]; intros s; simpl; [| eapply le_refl ].
  peel ltac:(eapply IH). peel ltac:(eapply step_le).
  peel ltac:(eapply fold_i_le; intros; peel ltac:(eapply add_v_le); eapply add_a_le).
  eapply add_v_le.
Qed.

Section Constraints.

  Variable (S : st).

  Local Notation vS := (vS S).
  Local Notation tgtS := (tgtS S).

  Fixpoint C (cur : tgt) (e : term.exp) : Prop :=
    match e with
    | term.Econstr x _ ys e =>
        PS.In (lcon x) (vS x) /\
        (forall i y, nth_error ys i = Some y -> PS.Subset (vS y) (nth i (gl (st_f S) x) PS.empty)) /\
        C cur e
    | term.Ecase y cl =>
        use_cl S false y /\
        (fix C_br (cl : list (term.ctor_tag * term.exp)) :=
           match cl with
           | [] => True
           | (_, e) :: cl => C cur e /\ C_br cl
           end) cl
    | term.Eproj x _ n y e =>
        use_cl S false y /\
        (forall z, PS.In (xI z) (vS y) -> PS.Subset (nth (N.to_nat n) (gl (st_f S) z) PS.empty) (vS x)) /\
        (PS.In ltop (vS y) -> PS.In ltop (vS x)) /\
        C cur e
    | term.Eletapp x f _ ys e => call_cl S f ys (TVar x) /\ C cur e
    | term.Efun B e => Cf B /\ C cur e
    | term.Eapp f _ ys => call_cl S f ys cur
    | term.Eprim_val _ _ e | term.Eprim _ _ _ e => C cur e
    | term.Ehalt x => PS.Subset (vS x) (tgtS cur)
    end
  with Cf (B : term.fundefs) : Prop :=
    match B with
    | term.Fcons g _ xs b B =>
        PS.In (lfun g) (vS g) /\
        (forall i x, nth_error xs i = Some x ->
                     i < length (gl (st_a S) g) /\ PS.Subset (nth i (gl (st_a S) g) PS.empty) (vS x)) /\
        C (TRet g) b /\ Cf B
    | term.Fnil => True
    end.

  Lemma step_C : forall e cur s, le_st S s -> le_st (step cur e s) S -> C cur e.
  Proof.
    eapply (exp_ind_br (fun e => forall cur s, le_st S s -> le_st (step cur e s) S -> C cur e)
                       (fun B => forall s, le_st S s -> le_st (step_fds B s) S -> Cf B));
      intros; simpl in *.
    - (* constr *)
      set (s1 := add_v x (PS.singleton (lcon x)) s) in *.
      set (s2 := fold_i (fun s i y => add_f x i (gv (st_v s) y) s) 0 ys s1) in *.
      assert (H12 : le_st s1 s2) by (eapply fold_i_le; intros; eapply add_f_le).
      assert (H2S : le_st s2 S) by (eapply le_trans; [ eapply step_le | eassumption ]).
      assert (HS1 : le_st S s1) by (eapply le_trans; [ eassumption | eapply add_v_le ]).
      split; [| split ].
      + eapply add_v_C; [ eapply le_trans; eauto |]. PSD.fsetdec.
      + intros i y Hy.
        destruct (fold_i_mid (fun s i y => add_f x i (gv (st_v s) y) s) (fun _ _ _ => add_f_le _ _ _ _) ys 0 s1 i y Hy)
          as (sb & Hb1 & Hb2).
        assert (HbS : le_st S sb) by (eapply le_trans; eauto).
        pose proof (add_f_C S x (0 + i) _ sb (le_trans _ _ _ Hb2 H2S)) as Hf. simpl in Hf.
        intros l Hl. eapply Hf. eapply (le_v _ _ HbS). exact Hl.
      + eapply H; [ eapply le_trans; eauto | eassumption ].
    - (* case *)
      pose proof (use_site_le false y s) as Hu.
      set (s1 := fst (use_site false y s)) in *.
      set (br := fix step_br (cl : list (term.ctor_tag * term.exp)) (s : st) :=
                   match cl with
                   | [] => s
                   | (_, e) :: cl => step_br cl (step cur e s)
                   end) in *.
      assert (Hbr : forall cl s, le_st s (br cl s)).
      { induction cl0 as [| [c e] cl0 IH]; intros s'; simpl; [ eapply le_refl |].
        eapply le_trans; [ eapply step_le | eapply IH ]. }
      split.
      + eapply use_site_C; [ eassumption |]. eapply le_trans; [ eapply Hbr | eassumption ].
      + assert (HS1 : le_st S s1) by (eapply le_trans; eauto).
        clear Hu. clearbody s1. revert s1 HS1 H1.
        induction H as [| [c e] cl He Hall IH ]; intros s1 HS1 Hs1; simpl in *; [ exact I |].
        split.
        * eapply He; [ exact HS1 | eapply le_trans; [ eapply Hbr | exact Hs1 ] ].
        * eapply IH; [| exact Hs1 ]. eapply le_trans; [ exact HS1 | eapply step_le ].
    - (* proj *)
      pose proof (use_site_le false y s) as Hu.
      set (s1 := fst (use_site false y s)) in *.
      set (G := fun l s => match l with
                           | xI z => add_v x (nth (N.to_nat n) (gl (st_f s) z) PS.empty) s
                           | xH => add_v x (PS.singleton ltop) s
                           | _ => s
                           end) in *.
      assert (HG : forall l s, le_st s (G l s)) by (intros l s'; destruct l; simpl; try eapply add_v_le; eapply le_refl).
      set (s2 := PS.fold G (gv (st_v s1) y) s1) in *.
      assert (H2S : le_st s2 S) by (eapply le_trans; [ eapply step_le | eassumption ]).
      assert (H1S : le_st s1 S) by (eapply le_trans; [ eapply ps_fold_le; exact HG | exact H2S ]).
      assert (HS1 : le_st S s1) by (eapply le_trans; eauto).
      split; [| split; [| split ] ].
      + exact (use_site_C S false y s ltac:(assumption) H1S).
      + intros z Hz. eapply (le_v _ _ HS1) in Hz.
        destruct (ps_fold_mid G HG (gv (st_v s1) y) s1 (xI z) Hz) as (sz & Hz1 & Hz2).
        assert (HSz : le_st S sz) by (eapply le_trans; eauto).
        pose proof (add_v_C S x _ sz (le_trans _ _ _ Hz2 H2S)) as Hv.
        intros l Hl. eapply Hv. eapply (le_f _ _ HSz). exact Hl.
      + intros Ht. eapply (le_v _ _ HS1) in Ht.
        destruct (ps_fold_mid G HG (gv (st_v s1) y) s1 xH Ht) as (sz & Hz1 & Hz2).
        pose proof (add_v_C S x _ sz (le_trans _ _ _ Hz2 H2S)) as Hv. eapply Hv. PSD.fsetdec.
      + eapply (H cur s2); [ eapply le_trans; [ exact HS1 | eapply ps_fold_le; exact HG ] | eassumption ].
    - (* letapp *)
      assert (HcS : le_st (call f ys (TVar x) s) S) by (eapply le_trans; [ eapply step_le | eassumption ]).
      split; [ eapply call_C; eassumption |].
      eapply H; [ eapply le_trans; [ eassumption | eapply call_le ] | eassumption ].
    - (* fun *)
      assert (HBS : le_st (step_fds B s) S) by (eapply le_trans; [ eapply step_le | eassumption ]).
      split; [ eapply H; eassumption |].
      eapply H0; [ eapply le_trans; [ eassumption | eapply step_fds_le ] | eassumption ].
    - (* app *) eapply call_C; eassumption.
    - eapply H; eassumption.
    - eapply H; eassumption.
    - (* halt *) intros l Hl. match goal with Hs : le_st S s, Ht : le_st (add_t _ _ _) S |- _ => eapply (add_t_C S cur _ s Ht); eapply (le_v _ _ Hs); exact Hl end.
    - (* fundefs *)
      set (s1 := add_v g (PS.singleton (lfun g)) s) in *.
      set (F := fun s i x => add_v x (nth i (gl (st_a s) g) PS.empty) (add_a g i PS.empty s)) in *.
      assert (HF : forall s i x, le_st s (F s i x))
        by (intros; unfold F; eapply le_trans; [ eapply add_a_le | eapply add_v_le ]).
      set (s2 := fold_i F 0 xs s1) in *.
      assert (H3S : le_st (step (TRet g) e s2) S) by (eapply le_trans; [ eapply step_fds_le | eassumption ]).
      assert (H2S : le_st s2 S) by (eapply le_trans; [ eapply step_le | eassumption ]).
      assert (H12 : le_st s1 s2) by (eapply fold_i_le; exact HF).
      assert (HS1 : le_st S s1) by (eapply le_trans; [ eassumption | eapply add_v_le ]).
      split; [| split; [| split ] ].
      + eapply add_v_C; [ eapply le_trans; eauto |]. PSD.fsetdec.
      + intros i x Hx.
        destruct (fold_i_mid F HF xs 0 s1 i x Hx) as (sb & Hb1 & Hb2). simpl in Hb2.
        assert (HSb : le_st S sb) by (eapply le_trans; eauto).
        pose proof (le_trans _ _ _ Hb2 H2S) as HbS. unfold F in HbS.
        split.
        * eapply add_a_C. eapply le_trans; [ eapply add_v_le | exact HbS ].
        * pose proof (add_v_C S x _ _ HbS) as Hv. intros l Hl. eapply Hv. eapply (le_a _ _ HSb). exact Hl.
      + eapply H; [ eapply le_trans; eauto | exact H3S ].
      + eapply H0; [| eassumption ]. eapply le_trans; [ eapply le_trans; eauto | eapply step_le ].
    - exact I.
  Qed.

  Definition labels_cl : Prop :=
    (forall g, PS.In (xO g) (XS S) ->
               escS S (gv (st_r S) g) /\
               forall i, i < length (gl (st_a S) g) -> PS.In ltop (nth i (gl (st_a S) g) PS.empty)) /\
    (forall z, PS.In (xI z) (XS S) -> forall i, escS S (nth i (gl (st_f S) z) PS.empty)).

  Lemma round_C e s :
    le_st S s -> le_st (round e s) S -> C TTop e /\ escS S (st_top S) /\ labels_cl.
  Proof.
    intros HS Hr. unfold round in Hr.
    set (s1 := step TTop e s) in *. set (s2 := escape (st_top s1) s1) in *.
    assert (Hel : forall l s, le_st s (expose_label l s)) by (intros; eapply expose_label_le).
    assert (H2S : le_st s2 S) by (eapply le_trans; [ eapply ps_fold_le; exact Hel | exact Hr ]).
    assert (H1S : le_st s1 S) by (eapply le_trans; [ eapply escape_le | exact H2S ]).
    assert (HS1 : le_st S s1) by (eapply le_trans; [ exact HS | eapply step_le ]).
    assert (HS2 : le_st S s2) by (eapply le_trans; [ exact HS1 | eapply escape_le ]).
    split; [| split ].
    - exact (step_C e TTop s HS H1S).
    - intros l Hl. eapply (escape_C S (st_top s1) s1 H2S). eapply (le_top _ _ HS1). exact Hl.
    - split.
      + intros g Hg. eapply (le_x _ _ HS2) in Hg.
        destruct (ps_fold_mid expose_label Hel (st_x s2) s2 (xO g) Hg) as (sl & Hl1 & Hl2).
        pose proof (le_trans _ _ _ Hl2 Hr) as HlS. simpl in HlS.
        assert (HSl : le_st S sl) by (eapply le_trans; eauto).
        split.
        * intros l Hl. eapply (escape_C S _ _ HlS). eapply (le_r _ _ HSl). exact Hl.
        * intros i Hi. eapply (expose_args_C S g _ sl); [ eapply le_trans; [ eapply escape_le | exact HlS ] |].
          pose proof (le_a_len _ _ HSl g). lia.
      + intros z Hz i. eapply (le_x _ _ HS2) in Hz.
        destruct (ps_fold_mid expose_label Hel (st_x s2) s2 (xI z) Hz) as (sl & Hl1 & Hl2).
        pose proof (le_trans _ _ _ Hl2 Hr) as HlS. simpl in HlS.
        assert (HSl : le_st S sl) by (eapply le_trans; eauto).
        destruct (Nat.lt_ge_cases i (length (gl (st_f sl) z))) as [Hi | Hi].
        * destruct (fold_left_mid (fun s A => escape A s) (fun _ _ => escape_le _ _) (gl (st_f sl) z) sl
                                  (nth i (gl (st_f sl) z) PS.empty) (nth_In _ _ Hi)) as (sA & HA1 & HA2).
          intros l Hl. eapply (escape_C S _ sA (le_trans _ _ _ HA2 HlS)). eapply (le_f _ _ HSl). exact Hl.
        * intros l Hl. eapply (le_f _ _ HSl) in Hl. rewrite nth_overflow in Hl by lia. PSD.fsetdec.
  Qed.

  Lemma init_C e b :
    le_st (init_from b e) S -> forall x, List.In x (PS.elements (identifiers.exp_fv e)) -> PS.In ltop (vS x).
  Proof.
    intros Hi x Hx. unfold init_from in Hi.
    match type of Hi with
    | le_st (fold_left ?g ?l ?s0) _ =>
        destruct (fold_left_mid g (fun _ _ => add_v_le _ _ _) l s0 x Hx) as (sx & _ & H2)
    end.
    eapply (add_v_C S x _ sx (le_trans _ _ _ H2 Hi)). apply PS.singleton_spec. reflexivity.
  Qed.

End Constraints.

Theorem solve_loop_from_C e b S :
  inv (vars_acc e (identifiers.exp_fv e)) (arity e) b ->
  solve_loop_from e (init_from b e) = Done S ->
  C S TTop e /\ escS S (st_top S) /\ labels_cl S /\
  (forall x, List.In x (PS.elements (identifiers.exp_fv e)) -> PS.In ltop (vS S x)).
Proof.
  intros Hb H. destruct (solve_loop_from_fix e _ S (init_from_inv e b Hb) H) as (s0 & Hi & H1 & H2 & Heq).
  edestruct (round_C S e s0) as (Hc & Ht & Hl); [ exact H2 | rewrite <- Heq; eapply le_refl |].
  split; [ exact Hc | split; [ exact Ht | split; [ exact Hl |] ] ].
  eapply (init_C S e b). eapply le_trans; eauto.
Qed.

Theorem solve_loop_C e S :
  solve_loop e = Done S ->
  C S TTop e /\ escS S (st_top S) /\ labels_cl S /\
  (forall x, List.In x (PS.elements (identifiers.exp_fv e)) -> PS.In ltop (vS S x)).
Proof. intros H. eapply (solve_loop_from_C e empty_st); [ eapply empty_inv | exact H ]. Qed.

(** * Merging makes the internal labels of a use site share a web *)

Lemma fold_set_in K m : forall iw x,
  In x K -> find_w (fold_left (fun iw l => M.set l m iw) K iw) x = m.
Proof.
  induction K as [| a K IH]; intros iw x Hx; [ easy |]. simpl.
  destruct (in_dec peq x K) as [HK | HK]; [ eapply IH; exact HK |].
  destruct Hx as [-> | Hx]; [| contradiction ].
  destruct (fold_set_find K m (M.set x m iw) x) as [[Hin _] | ->]; [ contradiction |].
  rewrite find_w_set. destruct (peq x x); congruence.
Qed.

Lemma iw_eqb_spec ls iw iw' : iw_eqb ls iw iw' = true -> forall l, In l ls -> find_w iw l = find_w iw' l.
Proof.
  unfold iw_eqb. intros H l Hl. eapply forallb_forall in H; eauto. eapply Pos.eqb_eq. exact H.
Qed.

Theorem merge_fix s ss ls iw :
  merge_loop s ss ls = Done iw ->
  forall fn y, In (fn, y) ss ->
  forall l1 l2, PS.In l1 (PS.diff (kind_labels fn (gv (st_v s) y)) (st_x s)) ->
                PS.In l2 (PS.diff (kind_labels fn (gv (st_v s) y)) (st_x s)) ->
                In l1 ls -> In l2 ls -> find_w iw l1 = find_w iw l2.
Proof.
  unfold merge_loop. intros H fn y Hy l1 l2 H1 H2 Hl1 Hl2.
  eapply loop_done_inv with (P := fun _ => True) in H; [| easy | easy ].
  destruct H as (iw0 & _ & -> & Heq).
  eapply in_split in Hy as (ss1 & ss2 & ->).
  set (iw1 := fold_left (merge_site s) ss1 iw0).
  set (iw2 := merge_site s iw1 (fn, y)).
  assert (E : fold_left (merge_site s) (ss1 ++ (fn, y) :: ss2) iw0 = fold_left (merge_site s) ss2 iw2)
    by (rewrite fold_left_app; reflexivity).
  rewrite E in Heq |- *.
  assert (H01 : mle iw0 iw1) by eapply merge_pass_le.
  assert (H12 : mle iw1 iw2) by eapply merge_site_le.
  assert (H2f : mle iw2 (fold_left (merge_site s) ss2 iw2)) by eapply merge_pass_le.
  assert (Hsame : forall l, In l ls -> find_w (fold_left (merge_site s) ss2 iw2) l = find_w iw2 l).
  { intros l Hl. eapply iw_eqb_spec in Heq; [| exact Hl ]. specialize (H01 l). specialize (H12 l). specialize (H2f l). lia. }
  rewrite (Hsame l1 Hl1), (Hsame l2 Hl2). unfold iw2, merge_site.
  destruct (PS.elements (PS.diff (kind_labels fn (gv (st_v s) y)) (st_x s))) as [| k K] eqn:HK.
  - eapply elements_In in H1. rewrite HK in H1. easy.
  - eapply elements_In in H1, H2. rewrite HK in H1, H2.
    rewrite !fold_set_in by assumption. reflexivity.
Qed.

Lemma fold_union_sub (L : list (positive * PS.t)) : forall acc,
  PS.Subset acc (fold_left (fun a p => PS.union a (snd p)) L acc) /\
  forall p, In p L -> PS.Subset (snd p) (fold_left (fun a p => PS.union a (snd p)) L acc).
Proof.
  induction L as [| q L IH]; intros acc; simpl; [ split; [ PSD.fsetdec | easy ] |].
  destruct (IH (PS.union acc (snd q))) as [H1 H2]. split; [ PSD.fsetdec |].
  intros p [-> | Hp]; [ PSD.fsetdec | eauto ].
Qed.

Lemma all_labels_in s y l : PS.In l (gv (st_v s) y) -> In l (all_labels s).
Proof.
  intros Hl. unfold all_labels. eapply elements_In. rewrite M.fold1_spec.
  unfold gv, getd in Hl. destruct (M.get y (st_v s)) as [A |] eqn:Hy; [| PSD.fsetdec ].
  eapply M.elements_correct in Hy.
  destruct (fold_union_sub (M.elements (st_v s)) PS.empty) as [_ H]. eapply (H _ Hy). exact Hl.
Qed.

Lemma getd_set_fold (g : lab -> positive) ls : forall m x,
  In x ls -> getd (fold_left (fun m l => M.set l (g l) m) ls m) 1%positive x = g x.
Proof.
  assert (Hout : forall ls m x, ~ In x ls ->
                 getd (fold_left (fun m l => M.set l (g l) m) ls m) 1%positive x = getd m 1%positive x).
  { induction ls0 as [| a ls0 IH]; intros m x Hx; simpl; [ reflexivity |].
    rewrite IH by (intros H; apply Hx; right; exact H). unfold getd. rewrite M.gso; [ reflexivity |].
    intros ->. apply Hx. left. reflexivity. }
  induction ls as [| a ls IH]; intros m x Hx; [ easy |]. simpl.
  destruct (in_dec peq x ls) as [Hin | Hin]; [ eapply IH; exact Hin |].
  destruct Hx as [-> | Hx]; [| contradiction ].
  rewrite Hout by exact Hin. unfold getd. rewrite M.gss. reflexivity.
Qed.

Lemma webs_of_spec e s l :
  In l (all_labels s) ->
  getd (webs_of e s) 1%positive l =
  find_w (match merge_loop s (sites e) (all_labels s) with Done iw | More iw => iw end) l.
Proof. intros Hl. unfold webs_of. cbv zeta. eapply getd_set_fold. exact Hl. Qed.

(** * The checker accepts the solution of the solver *)

Lemma forall_i_complete {A} (p : nat -> A -> bool) l : forall n,
  (forall i a, nth_error l i = Some a -> p (n + i) a = true) -> forall_i p n l = true.
Proof.
  induction l as [| a l IH]; intros n H; simpl; [ reflexivity |].
  eapply andb_true_intro. split.
  - specialize (H 0 a eq_refl). rewrite Nat.add_0_r in H. exact H.
  - eapply IH. intros i b Hb. specialize (H (Datatypes.S i) b Hb). rewrite <- Nat.add_succ_comm in H. exact H.
Qed.

Lemma sub_b_fin A B : PS.Subset A B -> sub_b (AFin A) (AFin B) = true.
Proof. intros H. simpl. eapply PS.subset_spec. exact H. Qed.

Section Check.

  Variables (w_con : web) (e0 : term.exp) (S : st).

  Definition sol0 : sol := fst (sol_of e0 S).

  Local Notation X := (st_x S).
  Local Notation vS := (vS S).

  Definition web_site (fn : bool) (y : var) : Prop :=
    forall l1 l2, PS.In l1 (vS y) -> kind fn l1 = true -> ~ PS.In l1 X ->
                  PS.In l2 (vS y) -> kind fn l2 = true -> ~ PS.In l2 X ->
                  getd (webs_of e0 S) 1%positive l1 = getd (webs_of e0 S) 1%positive l2.

  Lemma fl_sol x : fl sol0 x = AFin (vS x).
  Proof.
    unfold fl, sol0, sol_of, impl_complete.vS, gv, getd. simpl. rewrite M.gmap1. destruct (M.get x (st_v S)); reflexivity.
  Qed.

  Lemma arg_sol g : getd (s_arg sol0) [] g = map AFin (gl (st_a S) g).
  Proof. unfold sol0, sol_of, gl, getd. simpl. rewrite M.gmap1. destruct (M.get g (st_a S)); reflexivity. Qed.

  Lemma fld_sol z : getd (s_fld sol0) [] z = map AFin (gl (st_f S) z).
  Proof. unfold sol0, sol_of, gl, getd. simpl. rewrite M.gmap1. destruct (M.get z (st_f S)); reflexivity. Qed.

  Lemma Fld_sol z i : Fld sol0 z i = AFin (nth i (gl (st_f S) z) PS.empty).
  Proof.
    unfold Fld. rewrite fld_sol. change (s_fdef sol0) with (AFin PS.empty).
    rewrite map_nth. reflexivity.
  Qed.

  Lemma Ret_sol g : Ret sol0 g = AFin (gv (st_r S) g).
  Proof. unfold Ret, sol0, sol_of, gv, getd. simpl. rewrite M.gmap1. destruct (M.get g (st_r S)); reflexivity. Qed.

  Lemma isex_sol l : isex sol0 l = PS.mem l X.
  Proof. reflexivity. Qed.

  Lemma Arg_sub g i A : PS.Subset A (nth i (gl (st_a S) g) PS.empty) -> sub_b (AFin A) (Arg sol0 g i) = true.
  Proof.
    unfold Arg. rewrite arg_sol. change (s_adef sol0) with AAll. intros H.
    destruct (Nat.lt_ge_cases i (length (gl (st_a S) g))) as [Hi | Hi].
    - rewrite (nth_indep _ AAll (AFin PS.empty)) by (rewrite length_map; exact Hi).
      rewrite map_nth. eapply sub_b_fin. exact H.
    - rewrite nth_overflow by (rewrite length_map; exact Hi). reflexivity.
  Qed.

  Lemma Arg_sub_r g i B :
    i < length (gl (st_a S) g) -> PS.Subset (nth i (gl (st_a S) g) PS.empty) B -> sub_b (Arg sol0 g i) (AFin B) = true.
  Proof.
    unfold Arg. rewrite arg_sol. change (s_adef sol0) with AAll. intros Hi H.
    rewrite (nth_indep _ AAll (AFin PS.empty)) by (rewrite length_map; exact Hi).
    rewrite map_nth. eapply sub_b_fin. exact H.
  Qed.

  Lemma esc_b_sol A : escS S A -> esc_b sol0 (AFin A) = true.
  Proof.
    intros H. simpl. eapply forallb_forall. intros l Hl. eapply elements_In in Hl.
    destruct (H l Hl) as [-> | Hx]; [ reflexivity |].
    eapply orb_true_intro. right. rewrite isex_sol. eapply PS.mem_spec. exact Hx.
  Qed.

  Lemma wcon_sol z : wcon w_con sol0 z = if PS.mem (xI z) X then w_con else Internal (getd (webs_of e0 S) 1%positive (xI z)).
  Proof. reflexivity. Qed.

  Lemma wfun_sol g t : wfun sol0 g t = if PS.mem (xO g) X then Exposed t else Internal (getd (webs_of e0 S) 1%positive (xO g)).
  Proof. reflexivity. Qed.

  Lemma mem_false l A : PS.mem l A = false -> ~ PS.In l A.
  Proof. intros H Hl. eapply PS.mem_spec in Hl. congruence. Qed.

  Lemma use_b_ok y : use_cl S false y -> web_site false y -> use_b w_con sol0 y (wuse w_con sol0 y) = true.
  Proof.
    intros Hu Hw. unfold use_b, wuse. rewrite !fl_sol. simpl ain_b.
    destruct (PS.mem ltop (vS y)) eqn:Ht.
    - eapply forallb_forall. intros l Hl. eapply elements_In in Hl. destruct l as [z | z |]; try reflexivity.
      + rewrite wcon_sol. erewrite (proj2 (PS.mem_spec _ _)); [ eapply web_eqb_refl |].
        eapply Hu; [ left; eapply PS.mem_spec; exact Ht | exact Hl | reflexivity ].
      + eapply web_eqb_refl.
    - destruct (List.find is_clab (PS.elements (vS y))) as [l0 |] eqn:Hf.
      + eapply find_some in Hf as [Hl0 Hk0]. eapply elements_In in Hl0.
        destruct l0 as [z0 | z0 |]; try discriminate.
        eapply forallb_forall. intros l Hl. eapply elements_In in Hl. destruct l as [z | z |]; try reflexivity.
        * eapply web_eqb_eq. rewrite !wcon_sol.
          destruct (PS.mem (xI z) X) eqn:Hz, (PS.mem (xI z0) X) eqn:Hz0; try reflexivity.
          -- exfalso. eapply mem_false in Hz0. apply Hz0. eapply Hu; [| exact Hl0 | reflexivity ].
             right. exists (xI z). split; [ exact Hl | split; [ reflexivity | eapply PS.mem_spec; exact Hz ] ].
          -- exfalso. eapply mem_false in Hz. apply Hz. eapply Hu; [| exact Hl | reflexivity ].
             right. exists (xI z0). split; [ exact Hl0 | split; [ reflexivity | eapply PS.mem_spec; exact Hz0 ] ].
          -- f_equal. eapply Hw; eauto using mem_false.
        * exfalso. eapply PS.mem_spec in Hl. unfold ltop in *. congruence.
      + eapply forallb_forall. intros l Hl. pose proof Hl as Hl'. eapply elements_In in Hl'.
        destruct l as [z | z |]; try reflexivity.
        * eapply find_none in Hf; [| exact Hl ]. discriminate.
        * exfalso. eapply PS.mem_spec in Hl'. unfold ltop in *. congruence.
  Qed.

  Lemma app_b_ok f t ys tg :
    call_cl S f ys tg -> web_site true f -> app_b sol0 f t (wapp sol0 f t) ys (AFin (tgtS S tg)) = true.
  Proof.
    intros (Hu & Hg & Hto & Hesc) Hw.
    set (w := wapp sol0 f t).
    assert (Hfun : forall g, PS.In (xO g) (vS f) -> wfun sol0 g t = w).
    { intros g Hgf. unfold w, wapp. rewrite fl_sol. simpl ain_b.
      destruct (PS.mem ltop (vS f)) eqn:Ht.
      - rewrite wfun_sol. erewrite (proj2 (PS.mem_spec _ _)); [ reflexivity |].
        eapply Hu; [ left; eapply PS.mem_spec; exact Ht | exact Hgf | reflexivity ].
      - destruct (List.find is_flab (PS.elements (vS f))) as [l0 |] eqn:Hf.
        + eapply find_some in Hf as [Hl0 Hk0]. eapply elements_In in Hl0.
          destruct l0 as [| g0 |]; try discriminate. rewrite !wfun_sol.
          destruct (PS.mem (xO g) X) eqn:Hz, (PS.mem (xO g0) X) eqn:Hz0; try reflexivity.
          * exfalso. eapply mem_false in Hz0. apply Hz0. eapply Hu; [| exact Hl0 | reflexivity ].
            right. exists (xO g). split; [ exact Hgf | split; [ reflexivity | eapply PS.mem_spec; exact Hz ] ].
          * exfalso. eapply mem_false in Hz. apply Hz. eapply Hu; [| exact Hgf | reflexivity ].
            right. exists (xO g0). split; [ exact Hl0 | split; [ reflexivity | eapply PS.mem_spec; exact Hz0 ] ].
          * f_equal. eapply Hw; eauto using mem_false.
        + eapply find_none in Hf; [| eapply elements_In; exact Hgf ]. discriminate. }
    assert (Htop : PS.In ltop (vS f) -> w = Exposed t).
    { intros Ht. unfold w, wapp. rewrite fl_sol. simpl ain_b. erewrite (proj2 (PS.mem_spec _ _)); eauto. }
    assert (Hexp : exposedb w = true ->
                   PS.In ltop (vS f) \/ exists g, PS.In (xO g) (vS f) /\ PS.In (xO g) X).
    { unfold w, wapp. rewrite fl_sol. simpl ain_b.
      destruct (PS.mem ltop (vS f)) eqn:Ht; [ intros _; left; eapply PS.mem_spec; exact Ht |].
      destruct (List.find is_flab (PS.elements (vS f))) as [l0 |] eqn:Hf; [| discriminate ].
      eapply find_some in Hf as [Hl0 Hk0]. eapply elements_In in Hl0.
      destruct l0 as [| g0 |]; try discriminate. rewrite exposedb_wfun. intros He.
      right. exists g0. split; [ exact Hl0 | eapply PS.mem_spec; exact He ]. }
    clearbody w. unfold app_b. rewrite fl_sol. eapply andb_true_intro. split.
    - eapply forallb_forall. intros l Hl. eapply elements_In in Hl. destruct l as [| g |]; try reflexivity.
      + destruct (Hg g Hl) as [Hargs Hret].
        repeat (eapply andb_true_intro; split).
        * rewrite (Hfun g Hl). eapply web_eqb_refl.
        * eapply forall_i_complete. intros i y Hy. rewrite fl_sol. eapply Arg_sub. eapply Hargs. exact Hy.
        * rewrite Ret_sol. eapply sub_b_fin. exact Hret.
      + eapply andb_true_intro. split; [ rewrite (Htop Hl); eapply web_eqb_refl |].
        simpl. eapply PS.mem_spec. eapply Hto. exact Hl.
    - destruct (exposedb w) eqn:He; [| reflexivity ]. simpl.
      eapply forallb_forall. intros y Hy. rewrite fl_sol. eapply esc_b_sol. eapply Hesc; eauto.
  Qed.

  Lemma proj_b_ok y n x :
    (forall z, PS.In (xI z) (vS y) -> PS.Subset (nth n (gl (st_f S) z) PS.empty) (vS x)) ->
    (PS.In ltop (vS y) -> PS.In ltop (vS x)) ->
    proj_b sol0 y n x = true.
  Proof.
    intros Hf Ht. unfold proj_b. rewrite fl_sol. eapply forallb_forall. intros l Hl. eapply elements_In in Hl.
    destruct l as [z | z |]; try reflexivity.
    - rewrite Fld_sol, fl_sol. eapply sub_b_fin. eapply Hf. exact Hl.
    - rewrite fl_sol. simpl. eapply PS.mem_spec. eapply Ht. exact Hl.
  Qed.

  Definition sites_ok (ss : list (bool * var)) : Prop :=
    forall fn y, In (fn, y) ss -> web_site fn y.

  Lemma sites_ok_app l1 l2 : sites_ok (l1 ++ l2) -> sites_ok l1 /\ sites_ok l2.
  Proof. intros H. split; intros fn y Hy; eapply H; eapply in_or_app; eauto. Qed.

  Lemma chk_ok : forall e cur, C S cur e -> sites_ok (sites e) -> chk w_con sol0 (AFin (tgtS S cur)) e = true.
  Proof.
    eapply (exp_ind_br (fun e => forall cur, C S cur e -> sites_ok (sites e) -> chk w_con sol0 (AFin (tgtS S cur)) e = true)
                       (fun B => Cf S B -> sites_ok (sites_fds B) -> chk_fds w_con sol0 B = true));
      intros; simpl in *;
      repeat match goal with H : _ /\ _ |- _ => destruct H end.
    - (* constr *)
      repeat (eapply andb_true_intro; split).
      + rewrite fl_sol. simpl. eapply PS.mem_spec. assumption.
      + eapply forall_i_complete. intros i y Hy. rewrite fl_sol, Fld_sol. eapply sub_b_fin. eauto.
      + eauto.
    - (* case *)
      eapply andb_true_intro. split.
      + eapply use_b_ok; [ assumption |]. eapply H1. left. reflexivity.
      + assert (Hs : sites_ok ((fix sites_br (cl : list (term.ctor_tag * term.exp)) :=
                                 match cl with
                                 | [] => []
                                 | (_, e) :: cl => sites e ++ sites_br cl
                                 end) cl))
          by (intros fn y' Hy'; eapply H1; right; exact Hy').
        clear H1. revert Hs.
        match goal with Hc : context [ C S cur ] |- _ => revert Hc end.
        induction H as [| [c e] cl He Hall IH ]; intros Hc Hs; simpl in *; [ reflexivity |].
        destruct Hc as [Hc1 Hc2]. eapply sites_ok_app in Hs as [Hs1 Hs2].
        eapply andb_true_intro. split; [ eapply He; eauto | eapply IH; eauto ].
    - (* proj *)
      repeat (eapply andb_true_intro; split).
      + eapply use_b_ok; [ assumption |]. eapply H1. left. reflexivity.
      + eapply proj_b_ok; assumption.
      + eapply H; [ assumption |]. intros fn y' Hy'. eapply H1. right. exact Hy'.
    - (* letapp *)
      eapply andb_true_intro. split.
      + rewrite fl_sol. eapply (app_b_ok f ft ys (TVar x)); [ assumption |]. eapply H1. left. reflexivity.
      + eapply H; [ assumption |]. intros fn y' Hy'. eapply H1. right. exact Hy'.
    - (* fun *)
      eapply sites_ok_app in H2 as [HB He].
      eapply andb_true_intro. split; eauto.
    - (* app *) eapply app_b_ok; [ assumption |]. eapply H0. left. reflexivity.
    - eauto.
    - eauto.
    - (* halt *) rewrite fl_sol. eapply sub_b_fin. assumption.
    - (* fundefs *)
      eapply sites_ok_app in H2 as [Hb HB].
      repeat (eapply andb_true_intro; split).
      + rewrite fl_sol. simpl. eapply PS.mem_spec. assumption.
      + eapply forall_i_complete. intros i x Hx. simpl. rewrite fl_sol.
        match goal with Hp : forall i x, nth_error xs i = Some x -> _ |- _ => destruct (Hp i x Hx) as [Hi Hsub] end.
        eapply Arg_sub_r; eauto.
      + rewrite Ret_sol. eapply (H (TRet g)); eauto.
      + eauto.
    - reflexivity.
  Qed.

  Lemma labels_b_ok : labels_cl S -> labels_b sol0 = true.
  Proof.
    intros [Hg Hz]. unfold labels_b. change (s_ex sol0) with (AFin X).
    eapply forallb_forall. intros l Hl. eapply elements_In in Hl. destruct l as [z | g |]; try reflexivity.
    - eapply andb_true_intro. split; [ reflexivity |]. rewrite fld_sol.
      eapply forallb_forall. intros A HA. eapply in_map_iff in HA as (A' & <- & HA').
      eapply In_nth with (d := PS.empty) in HA' as (i & Hi & <-). eapply esc_b_sol. eapply Hz. exact Hl.
    - destruct (Hg g Hl) as [Hr Ha].
      repeat (eapply andb_true_intro; split).
      + rewrite Ret_sol. eapply esc_b_sol. exact Hr.
      + reflexivity.
      + rewrite arg_sol. eapply forallb_forall. intros A HA. eapply in_map_iff in HA as (A' & <- & HA').
        eapply In_nth with (d := PS.empty) in HA' as (i & Hi & <-). simpl. eapply PS.mem_spec. eauto.
  Qed.

End Check.

(** The solution of the solver passes the check. *)
Theorem check_solve w_con e s R : solve e = Some (s, R) -> check w_con s R e = true.
Proof.
  unfold solve. destruct (solve_loop e) as [S | S] eqn:Hl; intros H; [| discriminate ].
  injection H as Hs HR. subst s R.
  change (check w_con (sol0 e S) (AFin (st_top S)) e = true).
  destruct (solve_loop_C e S Hl) as (Hc & Ht & Hlab & Hfv).
  assert (Hw : sites_ok e S (sites e)).
  { intros fn y Hy l1 l2 H1 Hk1 Hx1 H2 Hk2 Hx2.
    assert (Hd : forall l, PS.In l (gv (st_v S) y) -> kind fn l = true -> ~ PS.In l (st_x S) ->
                           PS.In l (PS.diff (kind_labels fn (gv (st_v S) y)) (st_x S))).
    { intros l Hl' Hk Hx. eapply PS.diff_spec. split; [ eapply kind_labels_spec; eauto | exact Hx ]. }
    rewrite !webs_of_spec by (eapply all_labels_in; eassumption).
    destruct (merge_done S (sites e) (all_labels S)) as [iw Hiw]. rewrite Hiw.
    eapply merge_fix; eauto using all_labels_in. }
  unfold check. repeat (eapply andb_true_intro; split).
  - eapply labels_b_ok. exact Hlab.
  - eapply esc_b_sol. exact Ht.
  - eapply (chk_ok w_con e S e TTop); eauto.
  - eapply forallb_forall. intros x Hx. rewrite fl_sol. simpl. eapply PS.mem_spec. eauto.
Qed.

(** So the analysis always uses the solution of the solver: the fallback to
    the trivial solution is never taken. *)
Theorem analyze_solve w_con e : exists s R, solve e = Some (s, R) /\ analyze w_con e = (s, R).
Proof.
  destruct (solve_some e) as [[s R] Hs]. exists s, R. split; [ exact Hs |].
  unfold analyze. rewrite Hs, (check_solve w_con e s R Hs). reflexivity.
Qed.

(** * The solver from a seed *)

Lemma ulabels_sound V l : PS.In l (ulabels V) -> lab_in V l.
Proof.
  unfold ulabels. rewrite PS.fold_spec.
  assert (Hg : forall xs U0, (forall x, List.In x xs -> PS.In x V) -> (forall l, PS.In l U0 -> lab_in V l) ->
                        PS.In l (fold_left (fun U x => PS.add (lfun x) (PS.add (lcon x) U)) xs U0) -> lab_in V l).
  { induction xs as [| a xs IH]; intros U0 Hxs HU0 Hl; simpl in *; [ eauto |].
    eapply IH; [ intros; eapply Hxs; now right | | exact Hl ].
    intros l' Hl'. apply PS.add_spec in Hl' as [-> | Hl']; [ eapply Hxs; now left |].
    apply PS.add_spec in Hl' as [-> | Hl']; [ eapply Hxs; now left | eauto ]. }
  eapply Hg.
  - intros x Hx. eapply elements_In. exact Hx.
  - intros l' Hl'. apply PS.singleton_spec in Hl'. subst. exact I.
Qed.

Lemma restrict_set_sok V A : sok V (restrict_set (ulabels V) A).
Proof.
  intros l Hl. unfold restrict_set in Hl. apply PS.filter_spec in Hl as [_ Hl]; [| intros ? ? ->; reflexivity ].
  eapply ulabels_sound. eapply PS.mem_spec. exact Hl.
Qed.

Lemma restrict_inv V N s : inv V N (restrict V (ulabels V) N s).
Proof.
  assert (Hset : forall (m : M.t PS.t) k,
             sok V (gv (M.map (fun k A => if PS.mem k V then restrict_set (ulabels V) A else PS.empty) m) k) /\
             (~ PS.In k V -> PS.Subset (gv (M.map (fun k A => if PS.mem k V then restrict_set (ulabels V) A else PS.empty) m) k) PS.empty)).
  { intros m k. unfold gv, getd. rewrite M.gmap. destruct (M.get k m) as [A |]; simpl.
    - destruct (PS.mem k V) eqn:Hk; split.
      + eapply restrict_set_sok.
      + intros Hn. exfalso. apply Hn. eapply PS.mem_spec. exact Hk.
      + eapply sok_empty.
      + intros _. PSD.fsetdec.
    - split; [ eapply sok_empty | intros _; PSD.fsetdec ]. }
  assert (Hlist : forall (m : M.t (list PS.t)) k,
             lok V N (gl (M.map (fun k l => if PS.mem k V then map (restrict_set (ulabels V)) (firstn N l) else []) m) k) /\
             (~ PS.In k V -> gl (M.map (fun k l => if PS.mem k V then map (restrict_set (ulabels V)) (firstn N l) else []) m) k = [])).
  { intros m k. unfold gl, getd. rewrite M.gmap. destruct (M.get k m) as [l |]; simpl.
    - destruct (PS.mem k V) eqn:Hk; split.
      + split; [ rewrite length_map, length_firstn; lia |].
        intros i. destruct (Nat.lt_ge_cases i (length (map (restrict_set (ulabels V)) (firstn N l)))) as [Hi | Hi].
        * eapply nth_In in Hi. eapply in_map_iff in Hi as (A & HA & _).
          rewrite <- HA. eapply restrict_set_sok.
        * rewrite nth_overflow by lia. eapply sok_empty.
      + intros Hn. exfalso. apply Hn. eapply PS.mem_spec. exact Hk.
      + eapply lok_nil.
      + reflexivity.
    - split; [ eapply lok_nil | reflexivity ]. }
  constructor; simpl; intros; try eapply Hset; try eapply Hlist; eauto; eapply restrict_set_sok.
Qed.

Theorem solve_seeded_done e seed : exists S, solve_seeded e seed = Done S.
Proof. eapply solve_loop_from_done. Qed.

(** From any seed, the solution passes the check. *)
Theorem check_seeded w_con e seed S :
  solve_seeded e seed = Done S ->
  check w_con (fst (sol_of e S)) (snd (sol_of e S)) e = true.
Proof.
  unfold solve_seeded. cbv zeta. intros Hl.
  change (check w_con (sol0 e S) (AFin (st_top S)) e = true).
  destruct (solve_loop_from_C e _ S (restrict_inv _ _ _) Hl) as (Hc & Ht & Hlab & Hfv).
  assert (Hw : sites_ok e S (sites e)).
  { intros fn y Hy l1 l2 H1 Hk1 Hx1 H2 Hk2 Hx2.
    rewrite !webs_of_spec by (eapply all_labels_in; eassumption).
    destruct (merge_done S (sites e) (all_labels S)) as [iw Hiw]. rewrite Hiw.
    assert (Hd : forall l, PS.In l (gv (st_v S) y) -> kind fn l = true -> ~ PS.In l (st_x S) ->
                           PS.In l (PS.diff (kind_labels fn (gv (st_v S) y)) (st_x S))).
    { intros l Hl' Hk Hx. eapply PS.diff_spec. split; [ eapply kind_labels_spec; eauto | exact Hx ]. }
    eapply merge_fix; eauto using all_labels_in. }
  unfold check. repeat (eapply andb_true_intro; split).
  - eapply labels_b_ok. exact Hlab.
  - eapply esc_b_sol. exact Ht.
  - eapply (chk_ok w_con e S e TTop); eauto.
  - eapply forallb_forall. intros x Hx. rewrite fl_sol. simpl. eapply PS.mem_spec. eauto.
Qed.
