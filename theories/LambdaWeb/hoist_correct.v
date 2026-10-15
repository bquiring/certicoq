(* Correctness of hoisting some bundles ([hoist.v]).

   CertiRocq's [hoisting.v] proves hoisting all the functions of a program
   whose functions are closed up to the hoisted functions, as after closure
   conversion.  Here only some bundles move to the top bundle, and the
   others stay where they are, with the hoisted bundles nested in their
   bodies removed.  The relation [Hoist S] generalizes [Erase_fundefs] with a
   constructor for the bundles that stay, and the side condition of the
   hoisted bundles, that their free variables are hoisted functions (the
   names [S] of the top bundle), is part of the relation. *)

Require Import Common.AstCommon Common.compM.
Require Import LambdaANF.term LambdaANF.term_util LambdaANF.identifiers LambdaANF.eval LambdaANF.env
        LambdaANF.ctx LambdaANF.logical_relations LambdaANF.Ensembles_util LambdaANF.List_util
        LambdaANF.map_util LambdaANF.tactics LambdaANF.algebra LambdaANF.closure_conversion_util
        LambdaANF.hoisting LambdaANF.set_util.
Require Import LambdaANF.bounds.
From CertiRocq.LambdaWeb Require Import hoist.
Require Import compcert.lib.Coqlib.
From Stdlib Require Import Lists.List NArith.BinNat Relations.Relations
     micromega.Lia Sets.Ensembles Classes.Morphisms.

Import ListNotations.

Close Scope Z_scope.

Section Rel.

  (** The names of the top bundle *)
  Variable (S : Ensemble var).

  Inductive Hoist : exp -> exp -> fundefs -> nat -> Prop :=
  | Hoist_Efun :
      forall e e' defs Be Bdefs Be_defs n m,
        occurs_free_fundefs defs \subset S ->
        Hoist e e' Be n ->
        Hoist_nested defs Bdefs m ->
        split_fds Be Bdefs Be_defs ->
        Hoist (Efun defs e) e' Be_defs (1 + max n m)
  | Keep_Efun :
      forall e e' defs defs' Be Bdefs Be_defs n m,
        Hoist e e' Be n ->
        Hoist_keep defs defs' Bdefs m ->
        split_fds Be Bdefs Be_defs ->
        Hoist (Efun defs e) (Efun defs' e') Be_defs (max n m)
  | Hoist_Econstr :
      forall x t ys e e' B n,
        Hoist e e' B n ->
        Hoist (Econstr x t ys e) (Econstr x t ys e') B n
  | Hoist_Ecase_nil :
      forall x, Hoist (Ecase x nil) (Ecase x nil) Fnil 0
  | Hoist_Ecase_cons :
      forall x c e e' tes tes' B B' B'' n m,
        Hoist (Ecase x tes) (Ecase x tes') B n ->
        Hoist e e' B' m ->
        split_fds B B' B'' ->
        Hoist (Ecase x ((c, e) :: tes)) (Ecase x ((c, e') :: tes')) B'' (max n m)
  | Hoist_Eproj :
      forall x tau N y e e' B n,
        Hoist e e' B n ->
        Hoist (Eproj x tau N y e) (Eproj x tau N y e') B n
  | Hoist_Eletapp :
      forall x f tau ys e e' B n,
        Hoist e e' B n ->
        Hoist (Eletapp x f tau ys e) (Eletapp x f tau ys e') B n
  | Hoist_Eapp :
      forall f ft xs, Hoist (Eapp f ft xs) (Eapp f ft xs) Fnil 0
  | Hoist_Eprim_val :
      forall x p e e' B n,
        Hoist e e' B n ->
        Hoist (Eprim_val x p e) (Eprim_val x p e') B n
  | Hoist_Eprim :
      forall x f ys e e' B n,
        Hoist e e' B n ->
        Hoist (Eprim x f ys e) (Eprim x f ys e') B n
  | Hoist_Ehalt :
      forall x, Hoist (Ehalt x) (Ehalt x) Fnil 0
  (** A hoisted bundle: its functions, with their bodies hoisted, join the
      functions hoisted from the bodies *)
  with Hoist_nested : fundefs -> fundefs -> nat -> Prop :=
  | Hoist_Fcons :
      forall f tau xs e e' defs B B' B'' n m,
        Hoist e e' B n ->
        Hoist_nested defs B' m ->
        split_fds B (Fcons f tau xs e' B') B'' ->
        Hoist_nested (Fcons f tau xs e defs) B'' (max n m)
  | Hoist_Fnil :
      Hoist_nested Fnil Fnil 0
  (** A bundle that stays, with its bodies hoisted *)
  with Hoist_keep : fundefs -> fundefs -> fundefs -> nat -> Prop :=
  | Keep_Fcons :
      forall f tau xs e e' defs defs' B B' B'' n m,
        Hoist e e' B n ->
        Hoist_keep defs defs' B' m ->
        split_fds B B' B'' ->
        Hoist_keep (Fcons f tau xs e defs) (Fcons f tau xs e' defs') B'' (max n m)
  | Keep_Fnil :
      Hoist_keep Fnil Fnil Fnil 0.

End Rel.

#[global] Hint Constructors Hoist Hoist_nested Hoist_keep : core.

(** Equalities of unions of sets, up to associativity and commutativity *)
Ltac sets_ac :=
  repeat match goal with
    | |- context [ bound_var (Ecase ?x ?l) ] =>
        let X := fresh "X" in set (X := bound_var (Ecase x l)) in *; clearbody X
    end;
  split; intros ?z ?Hz;
  repeat match goal with
    | H : In _ (Union _ _ _) _ |- _ => destruct H
    | H : In _ (bound_var_fundefs Fnil) _ |- _ => inv H
    | H : In _ (Empty_set _) _ |- _ => inv H
    end;
  eauto 20 using Union_introl, Union_intror.

(** * Bound variables *)

Lemma Hoist_bound_var_mut S :
  (forall e e' B m, Hoist S e e' B m -> bound_var e <--> bound_var e' :|: bound_var_fundefs B) /\
  (forall B, (forall B' m, Hoist_nested S B B' m -> bound_var_fundefs B <--> bound_var_fundefs B') /\
             (forall B' Bc m, Hoist_keep S B B' Bc m ->
                              bound_var_fundefs B <--> bound_var_fundefs B' :|: bound_var_fundefs Bc)).
Proof.
  exp_defs_induction IHe IHl IHB; try (destruct IHB as [IHn IHk]);
    try (split; [ intros B' m Hr | intros B' Bc m Hr ]; inv Hr);
    try (intros e' B m Hr; inv Hr);
    repeat normalize_bound_var;
    repeat match goal with
      | H : Hoist _ ?a _ _ _, IH : forall e' B m, Hoist _ ?a e' B m -> _ |- _ => rewrite (IH _ _ _ H); clear H
      | H : Hoist_nested _ ?a _ _, IH : forall B' m, Hoist_nested _ ?a B' m -> _ |- _ => rewrite (IH _ _ H); clear H
      | H : Hoist_keep _ ?a _ _ _, IH : forall B' Bc m, Hoist_keep _ ?a B' Bc m -> _ |- _ =>
          rewrite (IH _ _ _ H); clear H
      | H : split_fds _ _ _ |- _ => rewrite (split_fds_bound_vars _ _ _ H); clear H
      end;
    repeat normalize_bound_var; try sets_ac.
Qed.

Lemma Hoist_bound_var S e e' B m :
  Hoist S e e' B m -> bound_var e <--> bound_var e' :|: bound_var_fundefs B.
Proof. eapply Hoist_bound_var_mut. Qed.

Lemma Hoist_nested_bound_var S B B' m :
  Hoist_nested S B B' m -> bound_var_fundefs B <--> bound_var_fundefs B'.
Proof. eapply Hoist_bound_var_mut. Qed.

Lemma Hoist_keep_bound_var S B B' Bc m :
  Hoist_keep S B B' Bc m -> bound_var_fundefs B <--> bound_var_fundefs B' :|: bound_var_fundefs Bc.
Proof. eapply Hoist_bound_var_mut. Qed.

(** * Unique bindings, by counting binders *)

Fixpoint bvl (e : exp) : list var :=
  match e with
  | Econstr x _ _ e | Eproj x _ _ _ e | Eletapp x _ _ _ e
  | Eprim_val x _ e | Eprim x _ _ e => x :: bvl e
  | Ecase _ cl => (fix bvl_br (cl : list (ctor_tag * exp)) :=
                     match cl with
                     | [] => []
                     | (_, e) :: cl => bvl e ++ bvl_br cl
                     end) cl
  | Efun B e => bvl_fds B ++ bvl e
  | Eapp _ _ _ | Ehalt _ => []
  end
with bvl_fds (B : fundefs) : list var :=
  match B with
  | Fcons f _ xs e B => f :: xs ++ bvl e ++ bvl_fds B
  | Fnil => []
  end.

Definition cnt (l : list var) (z : var) : nat := count_occ Pos.eq_dec l z.

Lemma cnt_nil z : cnt [] z = 0.
Proof. reflexivity. Qed.

Lemma cnt_cons x l z : cnt (x :: l) z = (if Pos.eq_dec x z then 1 else 0) + cnt l z.
Proof. unfold cnt. simpl. destruct (Pos.eq_dec x z); lia. Qed.

Lemma cnt_app l1 l2 z : cnt (l1 ++ l2) z = cnt l1 z + cnt l2 z.
Proof. unfold cnt. apply count_occ_app. Qed.

Lemma cnt_In l z : 0 < cnt l z <-> List.In z l.
Proof. unfold cnt. rewrite (count_occ_In Pos.eq_dec). split; lia. Qed.

Lemma cnt_not_In l z : cnt l z = 0 <-> ~ List.In z l.
Proof. unfold cnt. symmetry. apply count_occ_not_In. Qed.

Lemma cnt_NoDup l : NoDup l <-> forall z, cnt l z <= 1.
Proof. unfold cnt. apply NoDup_count_occ. Qed.

Lemma bvl_Ecase_cons x c e l : bvl (Ecase x ((c, e) :: l)) = bvl e ++ bvl (Ecase x l).
Proof. reflexivity. Qed.

Lemma In_Union_iff (A B : Ensemble var) z : z \in (A :|: B) <-> z \in A \/ z \in B.
Proof. split; [ intros H; inv H; auto | intros [H | H]; [ left | right ]; auto ]. Qed.

Lemma In_Singleton_iff (x z : var) : z \in [set x] <-> x = z.
Proof. split; [ intros H; inv H; auto | intros H; subst; constructor ]. Qed.

Lemma In_FromList_iff (l : list var) z : z \in FromList l <-> List.In z l.
Proof. reflexivity. Qed.

Lemma In_Empty_iff z : z \in Empty_set var <-> False.
Proof. split; [ intros H; inv H | contradiction ]. Qed.

Lemma bvl_correct :
  (forall e z, List.In z (bvl e) <-> z \in bound_var e) /\
  (forall B z, List.In z (bvl_fds B) <-> z \in bound_var_fundefs B).
Proof.
  exp_defs_induction IHe IHl IHB; intros z;
    rewrite ?bvl_Ecase_cons; simpl bvl; simpl bvl_fds; repeat normalize_bound_var;
    cbn [List.In];
    rewrite ?in_app_iff, ?In_Union_iff, ?In_Singleton_iff, ?In_FromList_iff, ?In_Empty_iff, ?IHe, ?IHl, ?IHB;
    tauto.
Qed.

Lemma nbv_cnt e x : ~ x \in bound_var e <-> cnt (bvl e) x = 0.
Proof. rewrite cnt_not_In, (proj1 bvl_correct). reflexivity. Qed.

Lemma nbvf_cnt B x : ~ x \in bound_var_fundefs B <-> cnt (bvl_fds B) x = 0.
Proof. rewrite cnt_not_In, (proj2 bvl_correct). reflexivity. Qed.

Lemma nfl_cnt l x : ~ x \in FromList l <-> cnt l x = 0.
Proof. rewrite cnt_not_In. reflexivity. Qed.

Lemma dis_cnt_gen (A B : Ensemble var) la lb :
  (forall z, List.In z la <-> z \in A) -> (forall z, List.In z lb <-> z \in B) ->
  (Disjoint _ A B <-> forall z, cnt la z = 0 \/ cnt lb z = 0).
Proof.
  intros HA HB. split.
  - intros [Hd] z. destruct (cnt la z) eqn:Ha; [ left; reflexivity | right ].
    apply cnt_not_In. intros Hb. apply (Hd z). constructor; [ apply HA | apply HB; exact Hb ].
    apply cnt_In. lia.
  - intros H. constructor. intros z Hz. inv Hz. apply HA in H0. apply HB in H1.
    apply cnt_In in H0. apply cnt_In in H1. destruct (H z); lia.
Qed.

Ltac to_cnt :=
  repeat match goal with
    | H : ~ In _ (bound_var _) _ |- _ => apply (proj1 (nbv_cnt _ _)) in H
    | H : ~ In _ (bound_var_fundefs _) _ |- _ => apply (proj1 (nbvf_cnt _ _)) in H
    | H : ~ In _ (FromList _) _ |- _ => apply (proj1 (nfl_cnt _ _)) in H
    | H : ~ (bound_var _) _ |- _ => apply (proj1 (nbv_cnt _ _)) in H
    | H : ~ (bound_var_fundefs _) _ |- _ => apply (proj1 (nbvf_cnt _ _)) in H
    | H : ~ (FromList _) _ |- _ => apply (proj1 (nfl_cnt _ _)) in H
    | H : NoDup _ |- _ => let H' := fresh in pose proof (proj1 (cnt_NoDup _) H) as H'; clear H
    | H : Disjoint _ (bound_var ?a) (bound_var ?b) |- _ =>
        let H' := fresh in pose proof (proj1 (dis_cnt_gen _ _ (bvl a) (bvl b) (proj1 bvl_correct a) (proj1 bvl_correct b)) H) as H'; clear H
    | H : Disjoint _ (bound_var ?a) (bound_var_fundefs ?b) |- _ =>
        let H' := fresh in pose proof (proj1 (dis_cnt_gen _ _ (bvl a) (bvl_fds b) (proj1 bvl_correct a) (proj2 bvl_correct b)) H) as H'; clear H
    | H : Disjoint _ (bound_var_fundefs ?a) (bound_var ?b) |- _ =>
        let H' := fresh in pose proof (proj1 (dis_cnt_gen _ _ (bvl_fds a) (bvl b) (proj2 bvl_correct a) (proj1 bvl_correct b)) H) as H'; clear H
    | H : Disjoint _ (bound_var_fundefs ?a) (bound_var_fundefs ?b) |- _ =>
        let H' := fresh in pose proof (proj1 (dis_cnt_gen _ _ (bvl_fds a) (bvl_fds b) (proj2 bvl_correct a) (proj2 bvl_correct b)) H) as H'; clear H
    | H : Disjoint _ (bound_var ?a) (FromList ?l) |- _ =>
        let H' := fresh in pose proof (proj1 (dis_cnt_gen _ _ (bvl a) l (proj1 bvl_correct a) (fun z => iff_refl _)) H) as H'; clear H
    | H : Disjoint _ (bound_var_fundefs ?a) (FromList ?l) |- _ =>
        let H' := fresh in pose proof (proj1 (dis_cnt_gen _ _ (bvl_fds a) l (proj2 bvl_correct a) (fun z => iff_refl _)) H) as H'; clear H
    end.

Ltac goal_cnt :=
  match goal with
  | |- ~ In _ (bound_var _) _ => apply (proj2 (nbv_cnt _ _))
  | |- ~ In _ (bound_var_fundefs _) _ => apply (proj2 (nbvf_cnt _ _))
  | |- ~ In _ (FromList _) _ => apply (proj2 (nfl_cnt _ _))
  | |- ~ (bound_var _) _ => apply (proj2 (nbv_cnt _ _))
  | |- ~ (bound_var_fundefs _) _ => apply (proj2 (nbvf_cnt _ _))
  | |- ~ (FromList _) _ => apply (proj2 (nfl_cnt _ _))
  | |- NoDup _ => apply (proj2 (cnt_NoDup _))
  | |- Disjoint _ (bound_var ?a) (bound_var ?b) =>
      apply (proj2 (dis_cnt_gen _ _ (bvl a) (bvl b) (proj1 bvl_correct a) (proj1 bvl_correct b)))
  | |- Disjoint _ (bound_var ?a) (bound_var_fundefs ?b) =>
      apply (proj2 (dis_cnt_gen _ _ (bvl a) (bvl_fds b) (proj1 bvl_correct a) (proj2 bvl_correct b)))
  | |- Disjoint _ (bound_var_fundefs ?a) (bound_var ?b) =>
      apply (proj2 (dis_cnt_gen _ _ (bvl_fds a) (bvl b) (proj2 bvl_correct a) (proj1 bvl_correct b)))
  | |- Disjoint _ (bound_var_fundefs ?a) (bound_var_fundefs ?b) =>
      apply (proj2 (dis_cnt_gen _ _ (bvl_fds a) (bvl_fds b) (proj2 bvl_correct a) (proj2 bvl_correct b)))
  | |- Disjoint _ (bound_var ?a) (FromList ?l) =>
      apply (proj2 (dis_cnt_gen _ _ (bvl a) l (proj1 bvl_correct a) (fun z => iff_refl _)))
  | |- Disjoint _ (bound_var_fundefs ?a) (FromList ?l) =>
      apply (proj2 (dis_cnt_gen _ _ (bvl_fds a) l (proj2 bvl_correct a) (fun z => iff_refl _)))
  end.

Ltac cnt_simpl := rewrite ?bvl_Ecase_cons in *; simpl bvl in *; simpl bvl_fds in *;
                  repeat (rewrite ?cnt_cons, ?cnt_app, ?cnt_nil in *).

Lemma ub_cnt :
  (forall e, unique_bindings e <-> forall z, cnt (bvl e) z <= 1) /\
  (forall B, unique_bindings_fundefs B <-> forall z, cnt (bvl_fds B) z <= 1).
Proof.
  exp_defs_induction IHe IHl IHB; split; intros H.
  all: try (inv H; to_cnt; rewrite ?IHe, ?IHl, ?IHB in *; intros z; cnt_simpl;
            repeat match goal with Hf : forall z, _ |- _ => specialize (Hf z) end;
            repeat match goal with |- context [ Pos.eq_dec ?a ?b ] => destruct (Pos.eq_dec a b) end;
            subst; lia).
  all: try (constructor;
            (try goal_cnt; rewrite ?IHe, ?IHl, ?IHB; try (intros z);
             match goal with |- context [ cnt _ ?w ] => specialize (H w) end; cnt_simpl;
             repeat match goal with Hd : context [ Pos.eq_dec ?a ?b ] |- _ => destruct (Pos.eq_dec a b) end;
             subst; try lia)).
Qed.

Lemma split_fds_cnt B1 B2 B3 :
  split_fds B1 B2 B3 -> forall z, cnt (bvl_fds B3) z = cnt (bvl_fds B1) z + cnt (bvl_fds B2) z.
Proof.
  induction 1; intros z; simpl bvl_fds; rewrite ?cnt_cons, ?cnt_app, ?cnt_nil;
    try rewrite (IHsplit_fds z); try rewrite ?cnt_cons, ?cnt_app; lia.
Qed.

Lemma Hoist_cnt_mut S :
  (forall e e' B m, Hoist S e e' B m -> forall z, cnt (bvl e) z = cnt (bvl e') z + cnt (bvl_fds B) z) /\
  (forall B, (forall B' m, Hoist_nested S B B' m -> forall z, cnt (bvl_fds B) z = cnt (bvl_fds B') z) /\
             (forall B' Bc m, Hoist_keep S B B' Bc m ->
                              forall z, cnt (bvl_fds B) z = cnt (bvl_fds B') z + cnt (bvl_fds Bc) z)).
Proof.
  exp_defs_induction IHe IHl IHB; try (destruct IHB as [IHn IHk]);
    try (split; [ intros B' m Hr | intros B' Bc m Hr ]; inv Hr);
    try (intros e' B m Hr; inv Hr); intros z;
    repeat match goal with
      | H : Hoist _ ?a _ _ _, IH : forall e' B m, Hoist _ ?a e' B m -> _ |- _ =>
          pose proof (IH _ _ _ H z); clear H
      | H : Hoist_nested _ ?a _ _, IH : forall B' m, Hoist_nested _ ?a B' m -> _ |- _ =>
          pose proof (IH _ _ H z); clear H
      | H : Hoist_keep _ ?a _ _ _, IH : forall B' Bc m, Hoist_keep _ ?a B' Bc m -> _ |- _ =>
          pose proof (IH _ _ _ H z); clear H
      | H : split_fds _ _ _ |- _ => pose proof (split_fds_cnt _ _ _ H z); clear H
      end;
    cnt_simpl; lia.
Qed.

Lemma Hoist_unique S e e' B m :
  Hoist S e e' B m -> unique_bindings e ->
  unique_bindings e' /\ unique_bindings_fundefs B /\ Disjoint _ (bound_var_fundefs B) (bound_var e').
Proof.
  intros Hr Hu. pose proof (proj1 (Hoist_cnt_mut S) _ _ _ _ Hr) as Hc.
  rewrite (proj1 ub_cnt) in Hu. split; [| split ].
  - apply (proj1 ub_cnt). intros z. specialize (Hc z). specialize (Hu z). lia.
  - apply (proj2 ub_cnt). intros z. specialize (Hc z). specialize (Hu z). lia.
  - goal_cnt. intros z. specialize (Hc z). specialize (Hu z). lia.
Qed.

Lemma Hoist_nested_unique S B B' m :
  Hoist_nested S B B' m -> unique_bindings_fundefs B -> unique_bindings_fundefs B'.
Proof.
  intros Hr Hu. pose proof (proj1 (proj2 (Hoist_cnt_mut S) B) _ _ Hr) as Hc.
  rewrite (proj2 ub_cnt) in *. intros z. specialize (Hc z). specialize (Hu z). lia.
Qed.

Lemma Hoist_keep_unique S B B' Bc m :
  Hoist_keep S B B' Bc m -> unique_bindings_fundefs B ->
  unique_bindings_fundefs B' /\ unique_bindings_fundefs Bc /\
  Disjoint _ (bound_var_fundefs Bc) (bound_var_fundefs B').
Proof.
  intros Hr Hu. pose proof (proj2 (proj2 (Hoist_cnt_mut S) B) _ _ _ Hr) as Hc.
  rewrite (proj2 ub_cnt) in Hu. split; [| split ].
  - apply (proj2 ub_cnt). intros z. specialize (Hc z). specialize (Hu z). lia.
  - apply (proj2 ub_cnt). intros z. specialize (Hc z). specialize (Hu z). lia.
  - goal_cnt. intros z. specialize (Hc z). specialize (Hu z). lia.
Qed.

(** * Names and definitions *)

Lemma Hoist_nested_name_in_fundefs S B B' m :
  Hoist_nested S B B' m -> name_in_fundefs B \subset name_in_fundefs B'.
Proof.
  intros Hr. induction Hr; [| sets ].
  match goal with Hs : split_fds _ _ _ |- _ => rewrite (split_fds_name_in_fundefs _ _ _ Hs) end.
  simpl. sets.
Qed.

Lemma Hoist_keep_name_in_fundefs S B B' Bc m :
  Hoist_keep S B B' Bc m -> name_in_fundefs B' <--> name_in_fundefs B.
Proof. intros Hr. induction Hr; simpl; [ rewrite IHHr | ]; reflexivity. Qed.

Lemma Hoist_nested_in_name S B B_hoist f tau xs e m :
  unique_bindings_fundefs B ->
  f \in name_in_fundefs B ->
  Hoist_nested S B B_hoist m ->
  find_def f B = Some (tau, xs, e) ->
  exists e' Be Bfuns n,
    find_def f B_hoist = Some (tau, xs, e') /\
    Hoist S e e' Be n /\
    split_fds Be Bfuns B_hoist /\ n <= m.
Proof.
  intros Hun Hin Hhoist Hfind.
  induction Hhoist.
  - assert (Hunn'' : unique_bindings_fundefs B'').
    { eapply Hoist_nested_unique; [| now eapply Hun ]. eapply Hoist_Fcons; eassumption. }
    inv Hun.
    destruct (peq f f0).
    * subst. simpl in Hfind. rewrite peq_true in Hfind. inv Hfind.
      do 4 eexists. split; [| split; [| split ]].
      erewrite split_fds_find_def; [ | | eassumption | ].
      simpl. rewrite peq_true. reflexivity.
      eapply unique_bindings_fundefs_unique_functions.
      eassumption. now left. eassumption.
      eassumption. eapply Nat.le_max_l.
    * subst. simpl in Hfind. rewrite peq_false in Hfind; eauto.
      inv Hin. match goal with Hs : _ \in [set _] |- _ => inv Hs; congruence end.
      edestruct IHHhoist as [e'' [Be' [Bfuns' [n1 [Hfind' [Hr [Hsplit Hleq]]]]]]];
        eauto.
      assert (Hfind'' : find_def f B'' = Some (tau, xs, e'')).
      { erewrite split_fds_find_def; [ | | eassumption | ].
        simpl. now rewrite peq_false; eauto.
        eapply unique_bindings_fundefs_unique_functions. eassumption.
        right. eapply Hoist_nested_name_in_fundefs. eassumption. eassumption. }
      match goal with Hs : split_fds B (Fcons _ _ _ _ _) B'' |- _ =>
        edestruct split_fds_trans as [Bf [Heq1 Heq2]]; [| eapply split_fds_sym; eapply Hs | ] end.
      eapply Right_f; eassumption.
      do 4 eexists. split; [| split; [| split ]].
      -- eassumption.
      -- eassumption.
      -- eassumption.
      -- eapply Nat.le_trans. eassumption. eapply Nat.le_max_r.
  - inv Hfind.
Qed.

Lemma Hoist_keep_find S B B' Bc m f tau xs e :
  Hoist_keep S B B' Bc m ->
  find_def f B = Some (tau, xs, e) ->
  exists e' Be Bo n,
    find_def f B' = Some (tau, xs, e') /\
    Hoist S e e' Be n /\
    split_fds Be Bo Bc /\ n <= m.
Proof.
  intros Hr. revert f tau xs e. induction Hr; intros g tau' xs' e1 Hf; simpl in Hf |- *; [| discriminate ].
  destruct (M.elt_eq g f).
  - inv Hf. do 4 eexists. split; [ reflexivity | split; [ eassumption | split; [ eassumption | lia ] ] ].
  - edestruct IHHr as [e2 [Be [Bo [n' [Hf' [Hh [Hs Hle]]]]]]]; [ eassumption |].
    edestruct split_fds_trans as [Bo' [Hs1 Hs2]]; [ exact Hs | eapply split_fds_sym; eassumption |].
    do 4 eexists. split; [ exact Hf' | split; [ exact Hh | split; [ exact Hs2 | lia ] ] ].
Qed.

Lemma Hoist_Ecase S x l1 l2 B n :
  Hoist S (Ecase x l1) (Ecase x l2) B n ->
  Forall2 (fun p1 p2 => fst p1 = fst p2) l1 l2.
Proof.
  revert x l2 B n; induction l1; intros x l2 B n Herase; inv Herase; eauto.
Qed.
Section Hoist_correct.

  Variable (cenv : ctor_env) (G : nat).

  Context {fuel : Type} {Hfuel : @fuel_resource fuel} {trace : Type} {Htrace : @trace_resource trace}.

  Context (P1 : nat -> PostT) (* Local *)
          (PG : PostGT) (* Global *)
          (HP : forall n, n <= G -> Post_properties cenv (P1 n) (P1 n) PG)
          (HPmon : forall n m, n <= m -> inclusion _ (P1 n) (P1 m))
          (Hpost_Efun_l : forall n, post_Efun_l (P1 n) (P1 (S n))).


  (** * Correctness of Erase_nested_fundefs *)
  Lemma Hoist_nested_correct S k B rho rho' B_hoist Bprev Ball n (Hleq : n <= G)
        (* IH for expresssions *)
        (IHe :
           forall m : nat,
             m < k ->
             forall (e e' : exp) (Bprev B Ball : fundefs) n (Hleq : n <= G) (rho rho' : env) (U L : nat),
               unique_bindings_fundefs Ball ->
               unique_bindings e ->
               preord_env_P cenv PG (occurs_free e) m rho rho' ->
               funs_inv_env Ball rho' ->
               split_fds Bprev B Ball ->
               Disjoint var (name_in_fundefs Ball) (bound_var e') ->
               Hoist (name_in_fundefs Ball) e e' B n -> preord_exp cenv (P1 n) PG m (e, rho) (e', rho')) :
    unique_bindings_fundefs Ball ->
    unique_bindings_fundefs B ->
    occurs_free_fundefs B \subset S ->
    (* initial environments are related *)
    preord_env_P cenv PG (S \\ name_in_fundefs B) k rho rho' ->
    (* assumptions about global funs *)
    funs_inv_env Ball rho' ->
    split_fds Bprev B_hoist Ball ->
    Disjoint var (name_in_fundefs Ball) (bound_var_fundefs B_hoist \\ name_in_fundefs B_hoist) ->
    occurs_free_fundefs B \subset name_in_fundefs Ball ->
    (* Erase fundefs *)
    Hoist_nested (name_in_fundefs Ball) B B_hoist n ->
    (* Environments after defining the function bundles *)
    preord_env_P cenv PG (name_in_fundefs B :|: S) k (def_funs B B rho rho) rho'.
  Proof.
    revert S B n Hleq rho rho' B_hoist Bprev Ball IHe.
    induction k as [k IHk] using lt_wf_rec1.
    intros S B n Hleq rho rho' B_hoist Bprev Ball IHe Hun1 Hun2
           Hsub Henv Hfuns Hsplit Hdis Hfvs Hhoist. assert (Hd' := HP). edestruct (Hd' n). eassumption.
    rewrite <- (Union_Setminus_Included (name_in_fundefs B) S (name_in_fundefs B)) at 1;
      [| tci | reflexivity ].
    eapply preord_env_P_union.
    - (* show it for the set of the added functions *)

      intros x Hin v Hget. rewrite def_funs_eq in Hget; eauto.
      inv Hget.

      destruct Hfuns as [rhoi Hfuns].

      eexists. split.
      eapply Hfuns. rewrite split_fds_name_in_fundefs; [| eassumption ]. right.
      eapply Hoist_nested_name_in_fundefs. eassumption. eassumption.

      rewrite preord_val_eq.
      intros vs1 vs2 j t xs1 e1 rho1' Heq1 Hf1 Hset1.
      edestruct Hoist_nested_in_name as [e2' [B2 [B2f [n1 [Hf2 [Hr2 [Hs2 Hleq']]]]]]];
        [| | | eapply Hf1 | ]; eauto.
      edestruct (@set_lists_length3 val (def_funs Ball Ball rhoi rhoi) xs1 vs2)
        as [rho2' Hset2].
      rewrite <- Heq1. eapply set_lists_length_eq. now eauto.
      do 3 eexists. split; [| split ].
      + erewrite split_fds_find_def; try eassumption.
        eapply unique_bindings_fundefs_unique_functions. eassumption.
        eapply Hoist_nested_name_in_fundefs; eassumption.
      + eauto.
      + intros Hlt Hall.
        eapply preord_exp_post_monotonic with (P1 := P1 n1). eapply Hd'. lia.

        assert (Hsplit' := Hsplit).
        eapply split_fds_sym in Hsplit.
        edestruct (split_fds_trans _ _ _ _ _ Hs2 Hsplit) as [Bprev' [Hs3 Hs4]].
        eapply IHe with (Ball := Ball) (Bprev := Bprev');
          last eassumption; try eassumption.
        * lia.
        * eapply unique_bindings_fun_in_fundefs.
          eapply find_def_correct. eassumption.
          eassumption.
        * eapply preord_env_P_antimon;
            [| eapply occurs_free_in_fun; eapply find_def_correct; eauto ].
          eapply preord_env_P_set_lists_l with (P1 := name_in_fundefs B :|: occurs_free_fundefs B);
            try solve [eauto].
          2:{ intros z Hnin Hinz. inv Hinz; eauto. contradiction. }
          clear Hs3 Hs4.
          (* eapply IHk to show that inner def_funs are related *)
          { eapply IHk with (Ball := Ball); last eassumption; try eassumption.
            - intros. eapply IHe; eauto. lia.
            - reflexivity.
            - intros z Hinz v Hgetz.
              inv Hinz.
              setoid_rewrite def_funs_eq; eauto.
              eexists; split; eauto.


              edestruct Henv as [v2 [Hget2 Hv2]]; eauto. constructor; eauto.
              rewrite Hfuns in Hget2. inv Hget2; eauto.
              eapply preord_val_monotonic. eassumption. lia.
              eapply Hfvs; eauto.
              eapply Hfvs; eauto.
            - eexists. intros f1 Hf. rewrite def_funs_eq. reflexivity.
              eassumption. }
        * eexists. intros f H1. erewrite <- set_lists_not_In; [| now eauto | ].
          rewrite def_funs_eq. reflexivity. eassumption.
          assert (Hun : Disjoint var (FromList xs1) (name_in_fundefs Ball)).
          { eapply unique_bindings_fun_in_fundefs; [| eassumption ].
            erewrite split_fds_fun_in_fundefs; [| eapply Hsplit ].
            left. eapply find_def_correct. eassumption. }
          intros Hc. eapply Hun. constructor. eassumption. eassumption.
        * eapply split_fds_sym. eassumption.
        * eapply Disjoint_Included_r; [| eassumption ].
          eapply Included_Setminus.

          eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption.
          eapply Hoist_nested_unique. eassumption. eassumption.

          eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eauto;
                                    eapply find_def_correct; eauto ].
          sets.
    - (* show if for S *)
      eapply preord_env_P_def_funs_not_in_P_l; [| sets ].
      eapply preord_env_P_antimon. eassumption. sets.
  Qed.

  Lemma funs_inv_env_def_funs Ball rho B0 B rho0 :
    funs_inv_env Ball rho -> Disjoint _ (name_in_fundefs Ball) (name_in_fundefs B) ->
    funs_inv_env Ball (def_funs B0 B rho0 rho).
  Proof.
    intros [rhoi Hf] Hd. exists rhoi. intros f Hin. rewrite def_funs_neq; [ eauto |].
    intros Hc. eapply Hd. constructor; eauto.
  Qed.

  Lemma funs_inv_env_set_lists Ball rho xs (vs : list val) rho' :
    funs_inv_env Ball rho -> Disjoint _ (name_in_fundefs Ball) (FromList xs) ->
    set_lists xs vs rho = Some rho' -> funs_inv_env Ball rho'.
  Proof.
    intros [rhoi Hf] Hd Hs. exists rhoi. intros f Hin. erewrite <- set_lists_not_In; [ eauto | eassumption |].
    intros Hc. eapply Hd. constructor; eauto.
  Qed.

  (** * Correctness of the bundles that stay *)
  Lemma Hoist_keep_correct S k B rho rho' B' Bc Bprev Ball n (Hleq : n <= G)
        (* IH for expresssions *)
        (IHe :
           forall m : nat,
             m < k ->
             forall (e e' : exp) (Bprev B Ball : fundefs) n (Hleq : n <= G) (rho rho' : env) (U L : nat),
               unique_bindings_fundefs Ball ->
               unique_bindings e ->
               preord_env_P cenv PG (occurs_free e) m rho rho' ->
               funs_inv_env Ball rho' ->
               split_fds Bprev B Ball ->
               Disjoint var (name_in_fundefs Ball) (bound_var e') ->
               Hoist (name_in_fundefs Ball) e e' B n -> preord_exp cenv (P1 n) PG m (e, rho) (e', rho')) :
    unique_bindings_fundefs Ball ->
    unique_bindings_fundefs B ->
    occurs_free_fundefs B \subset S ->
    preord_env_P cenv PG (S \\ name_in_fundefs B) k rho rho' ->
    funs_inv_env Ball rho' ->
    split_fds Bprev Bc Ball ->
    Disjoint var (name_in_fundefs Ball) (bound_var_fundefs B') ->
    Hoist_keep (name_in_fundefs Ball) B B' Bc n ->
    preord_env_P cenv PG (name_in_fundefs B :|: S) k (def_funs B B rho rho) (def_funs B' B' rho' rho').
  Proof.
    revert S B n Hleq rho rho' B' Bc Bprev Ball IHe.
    induction k as [k IHk] using lt_wf_rec1.
    intros S B n Hleq rho rho' B' Bc Bprev Ball IHe Hun1 Hun2 Hsub Henv Hfuns Hsplit Hdis Hhoist.
    assert (Hnames := Hoist_keep_name_in_fundefs _ _ _ _ _ Hhoist).
    rewrite <- (Union_Setminus_Included (name_in_fundefs B) S (name_in_fundefs B)) at 1;
      [| tci | reflexivity ].
    eapply preord_env_P_union.
    - intros x Hin v Hget. rewrite def_funs_eq in Hget; eauto. inv Hget.
      eexists. split.
      { rewrite def_funs_eq. reflexivity. eapply Hnames. eassumption. }
      rewrite preord_val_eq.
      intros vs1 vs2 j t xs1 e1 rho1' Heq1 Hf1 Hset1.
      edestruct Hoist_keep_find as [e2' [Be [Bo [n1 [Hf2 [Hr2 [Hs2 Hleq']]]]]]]; [ eassumption | eassumption | ].
      edestruct (@set_lists_length3 val (def_funs B' B' rho' rho') xs1 vs2) as [rho2' Hset2].
      { rewrite <- Heq1. eapply set_lists_length_eq. now eauto. }
      do 3 eexists. split; [ exact Hf2 | split; [ symmetry; exact Hset2 |] ].
      intros Hlt Hall.
      eapply preord_exp_post_monotonic with (P1 := P1 n1). eapply HP. lia.
      edestruct split_fds_trans as [Bprev' [Hs3 Hs4]]; [ exact Hs2 | eapply split_fds_sym; exact Hsplit |].
      assert (HB'bv : bound_var e2' :|: FromList xs1 :|: name_in_fundefs B' \subset bound_var_fundefs B').
      { eapply Union_Included; [ eapply Union_Included |].
        - eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eassumption ]. sets.
        - eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eapply find_def_correct; eassumption ]. sets.
        - eapply name_in_fundefs_bound_var_fundefs. }
      eapply IHe with (Ball := Ball) (Bprev := Bprev'); try eassumption.
      + lia.
      + eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption. eassumption.
      + eapply preord_env_P_antimon; [| eapply occurs_free_in_fun; eapply find_def_correct; eauto ].
        eapply preord_env_P_set_lists_l with (P1 := name_in_fundefs B :|: occurs_free_fundefs B);
          try solve [ eauto ].
        2:{ intros z Hnin Hinz. inv Hinz; eauto. contradiction. }
        eapply IHk with (Ball := Ball); last eassumption; try eassumption.
        * intros. eapply IHe; eauto. lia.
        * reflexivity.
        * eapply preord_env_P_antimon. eapply preord_env_P_monotonic; [| eassumption ]. lia. sets.
      + eapply funs_inv_env_set_lists; [ | | eassumption ].
        * eapply funs_inv_env_def_funs. eassumption.
          eapply Disjoint_Included_r; [| eassumption ]. eapply Included_trans; [| exact HB'bv ]. sets.
        * eapply Disjoint_Included_r; [| eassumption ]. eapply Included_trans; [| exact HB'bv ]. sets.
      + eapply split_fds_sym. eassumption.
      + eapply Disjoint_Included_r; [| eassumption ]. eapply Included_trans; [| exact HB'bv ]. sets.
    - eapply preord_env_P_def_funs_not_in_P_l; [| sets ].
      eapply preord_env_P_def_funs_not_in_P_r; [| rewrite Hnames; sets ].
      eapply preord_env_P_antimon. eassumption. sets.
  Qed.

  (** * Correctness of Erase_fundefs *)

  Lemma hoist_correct k e e' Bprev B Ball rho rho' n (Hleq : n <= G) :
    unique_bindings_fundefs Ball ->
    unique_bindings e ->
    (* environments are related *)
    preord_env_P cenv PG (occurs_free e) k rho rho' ->
    (* Hoisted functions are already defined *)
    funs_inv_env Ball rho' ->
    split_fds Bprev B Ball ->
    (* And will not be shadowed by other vars *)
    Disjoint _ (name_in_fundefs Ball) (bound_var e') ->
    (* the FVs of the original functions are in the global fundefs *)
    (* Hoisting *)
    Hoist (name_in_fundefs Ball) e e' B n ->
    preord_exp cenv (P1 n) PG k (e, rho) (e', rho').
  Proof.
    revert e e' Bprev B Ball n Hleq rho rho'.
    induction k as [k IHk] using lt_wf_rec1.
    intros e; revert k IHk; induction e using exp_ind';
      intros k IHk e' Bprev B Ball m Hleq' rho rho' Hun1 Hun2 Henv Hfuns Hsplit Hdis Hhoist;
      inv Hhoist; inv Hun2; try (assert (Hd' := HP m); destruct Hd'; try lia).
    - (* Econstr *)
      eapply preord_exp_constr_compat.
      + now eauto.
      + now eauto.
      + eapply Forall2_same. intros x Hin. eapply Henv.
        now constructor.
      + intros m1 vs1 vs2 Hlt Hall.
        eapply IHk; [ eassumption | eassumption | eassumption | | | | eassumption | | ].
        * eassumption.
        * eapply preord_env_P_extend.
          -- eapply preord_env_P_antimon.
             eapply preord_env_P_monotonic; [| eassumption ]. lia.
             normalize_occurs_free. sets.
          -- rewrite preord_val_eq. constructor; eauto.
        * eapply funs_inv_env_set. eassumption.
          eapply Disjoint_In_l. eapply Disjoint_sym. eassumption.
          normalize_bound_var; sets.
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var; sets.
        * eassumption.
    - (* Ecase nil *)
      eapply preord_exp_case_nil_compat. eapply HP. lia.
    - (* Ecase cons *)
      eapply split_fds_sym in H8.
      edestruct split_fds_trans as [Bnew [Hs1 Hs2]].
      now eapply H8. eapply split_fds_sym. eassumption.
      eapply split_fds_sym in H8.
      edestruct split_fds_trans as [Bnew' [Hs1' Hs2']].
      now eapply H8. eapply split_fds_sym. eassumption.
      eapply preord_exp_case_cons_compat; eauto.
      + eapply HP. lia.
      + eapply HP. lia.
      + eapply HP. lia.
      + eapply Hoist_Ecase. eassumption.
      + intros m Hlt.
        eapply preord_exp_post_monotonic. eapply HPmon with (n := m0). lia.
        eapply IHk; last eassumption; eauto.
        * lia.
        * eapply preord_env_P_antimon.
          eapply preord_env_P_monotonic; [| eassumption ]. lia.
          normalize_occurs_free; sets.
        * apply split_fds_sym. eassumption.
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var; sets.
      + eapply preord_exp_post_monotonic. eapply HPmon with (n := n). lia.
        eapply IHe0; last eassumption; eauto.
        * lia.
        * eapply preord_env_P_antimon. eassumption.
          normalize_occurs_free; sets.
        * apply split_fds_sym. eassumption.
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var; sets.
    - (* Eproj *)
      eapply preord_exp_proj_compat.
      + now eauto.
      + now eauto.
      + eapply Henv. eauto.
      + intros m1 vs1 vs2 Hlt Hall.
        eapply IHk; [ eassumption | eassumption | eassumption | | | | eassumption | | ].
        * eassumption.
        * eapply preord_env_P_extend.
          -- eapply preord_env_P_antimon.
             eapply preord_env_P_monotonic; [| eassumption ]. lia.
             normalize_occurs_free. sets.
          -- eassumption.
        * eapply funs_inv_env_set. eassumption.
          eapply Disjoint_In_l. eapply Disjoint_sym. eassumption.
          normalize_bound_var; sets.
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var; sets.
        * eassumption.
    - (* Eletapp *)
      eapply preord_exp_letapp_compat.
      + now eauto.
      + now eauto.
      + now eauto.
      + eapply Henv. constructor. now left.
      + eapply Forall2_same. intros z Hin. eapply Henv.
        constructor. now right.
      + intros m1 v1 v2 hlew Hrel.
        eapply IHk; [ eassumption | eassumption | eassumption | | | | eassumption | | ].
        * eassumption.
        * eapply preord_env_P_extend.
          -- eapply preord_env_P_antimon.
             eapply preord_env_P_monotonic; [| eassumption ]. lia.
             normalize_occurs_free. sets.
          -- eassumption.
        * eapply funs_inv_env_set. eassumption.
          eapply Disjoint_In_l. eapply Disjoint_sym. eassumption.
          normalize_bound_var; sets.
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var; sets.
        * eassumption.
    - (* Efun -- the only non trivial case *)
      match goal with Hs : split_fds _ _ B |- _ => rename Hs into Hsb end.
      eapply preord_exp_Efun_l.
      + eapply HP. lia.
      + now eauto.
      + eapply split_fds_sym in Hsplit.
        eapply split_fds_sym in Hsb.
        edestruct split_fds_trans as [Bnew [Hs1 Hs2]]. now eapply Hsb. eassumption.
        eapply split_fds_sym in Hsb.
        edestruct split_fds_trans as [Bnew' [Hs1' Hs2']]. now eapply Hsb. eassumption.
        eapply preord_exp_post_monotonic. eapply HPmon with (n := n). lia.

        eapply IHe with (Ball := Ball); [ | | eassumption | eassumption | | | | | eassumption ].
        * intros. eapply IHk; eauto. lia.
        * lia.
        * eapply preord_env_P_antimon.
          -- { eapply Hoist_nested_correct with (S := occurs_free_fundefs f2 :|: occurs_free e);
               [ | | | | | | | | | | eassumption ].
               - lia.
               - intros. eapply IHk; eauto. lia.
               - eapply Hun1.
               - eassumption.
               - sets.
               - eapply preord_env_P_antimon. eapply preord_env_P_monotonic; [| eassumption ].
                 lia. normalize_occurs_free; sets.
                 rewrite Setminus_Union_distr. sets.
               - eassumption.
               - eapply split_fds_sym.  eassumption.
               - edestruct Hoist_unique as [? [? ?]];
                   [ eapply Hoist_Efun; eassumption | constructor; eassumption | ].

                 rewrite (split_fds_name_in_fundefs _ _ _ Hs2). eapply Union_Disjoint_l.
                 now sets.
                 eapply split_fds_unique_bindings_fundefs_l in Hs2. destructAll.
                 eapply Disjoint_Included_l. eapply name_in_fundefs_bound_var_fundefs. sets.
                 eassumption.
               - eassumption. }
          -- sets.
        * eassumption.
        * eapply split_fds_sym. eassumption.
        * eapply Disjoint_Included_r; [| eassumption ]. reflexivity.
    - (* Efun, the bundle stays *)
      match goal with
      | Hk : Hoist_keep _ f2 _ _ _, He : Hoist _ e _ _ _, Hs : split_fds _ _ B |- _ =>
          rename Hk into Hk0; rename He into He0; rename Hs into Hs0
      end.
      edestruct split_fds_trans as [X [HX1 HX2]]; [ exact Hs0 | eapply split_fds_sym; exact Hsplit |].
      edestruct split_fds_trans as [Y [HY1 HY2]]; [ eapply split_fds_sym; exact Hs0 | eapply split_fds_sym; exact Hsplit |].
      assert (Hdis1 : Disjoint var (name_in_fundefs Ball) (bound_var_fundefs defs'))
        by (eapply Disjoint_Included_r; [| exact Hdis ]; normalize_bound_var; sets).
      assert (Hdis2 : Disjoint var (name_in_fundefs Ball) (bound_var e'0))
        by (eapply Disjoint_Included_r; [| exact Hdis ]; normalize_bound_var; sets).
      destruct (HP _ Hleq') as [_ _ Hpfun _ _ _ _ _ Hpoot _ _].
      eapply preord_exp_fun_compat; [ eapply Hpoot | eapply Hpfun |].
      eapply preord_exp_post_monotonic; [ eapply HPmon with (n := n); lia |].
      eapply IHe with (Ball := Ball) (Bprev := X); try eassumption.
      + intros. eapply IHk; eauto. lia.
      + lia.
      + eapply preord_env_P_antimon.
        * eapply Hoist_keep_correct with (S := occurs_free_fundefs f2 :|: occurs_free e) (Ball := Ball)
                                          (Bprev := Y) (n := m0) (Bc := Bdefs); try eassumption.
          -- lia.
          -- intros. eapply IHk; eauto. lia.
          -- sets.
          -- eapply preord_env_P_antimon; [ eapply preord_env_P_monotonic; [| eassumption ]; lia |].
             normalize_occurs_free. rewrite Setminus_Union_distr. sets.
          -- eapply split_fds_sym. eassumption.
        * sets.
      + eapply funs_inv_env_def_funs; [ eassumption |].
        eapply Disjoint_Included_r; [| exact Hdis1 ]. eapply name_in_fundefs_bound_var_fundefs.
      + eapply split_fds_sym. eassumption.
    - (* Eapp *)
      eapply preord_exp_app_compat.
      + eapply HP. lia.
      + eapply HP. lia.
      + eapply Henv. constructor.
      + eapply Forall2_same. intros z Hin. eapply Henv.
        now constructor.
    - (* Eprim *)
      eapply preord_exp_prim_val_compat.
      + now eauto.
    - (* Eprim *)
      eapply preord_exp_prim_compat.
      + now eauto.
      + eapply Forall2_same. intros x Hin. eapply Henv.
        now constructor.
    - (* Ehalt *)
      eapply preord_exp_halt_compat; eauto.
      + eapply HP. lia.
      + eapply HP. lia.
  Qed.

End Hoist_correct.

(** * The implementation *)

Lemma split_fds_append_l P B1 B2 B3 :
  split_fds B1 B2 B3 -> split_fds (fundefs_append P B1) B2 (fundefs_append P B3).
Proof. intros H. induction P; simpl; [ constructor; exact IHP | exact H ]. Qed.

Lemma split_fds_append_r P B1 B2 B3 :
  split_fds B1 B2 B3 -> split_fds B1 (fundefs_append P B2) (fundefs_append P B3).
Proof. intros H. induction P; simpl; [ constructor; exact IHP | exact H ]. Qed.

Lemma split_compose Bb acc acc1 Be acc2 :
  split_fds Bb acc acc1 -> split_fds Be acc1 acc2 ->
  exists Z, split_fds Be Bb Z /\ split_fds Z acc acc2.
Proof.
  intros H1 H2. edestruct split_fds_trans as [Z [HZ1 HZ2]];
    [ eapply split_fds_sym; exact H1 | eapply split_fds_sym; exact H2 |].
  exists Z. split; eapply split_fds_sym; eassumption.
Qed.

Lemma Hoist_keep_nested S B B' Bc m :
  Hoist_keep S B B' Bc m -> Hoist_nested S B (fundefs_append B' Bc) m.
Proof.
  intros Hr. induction Hr; simpl; [| constructor ].
  econstructor; [ eassumption | eassumption |].
  constructor. eapply split_fds_append_r. eassumption.
Qed.

Lemma subset_FromSet s1 s2 : PS.subset s1 s2 = true -> FromSet s1 \subset FromSet s2.
Proof.
  intros H z Hz. apply PS.subset_spec in H.
  eapply (FromSet_complete (FromSet s2) s2 z); [ reflexivity |]. apply H.
  eapply (FromSet_sound (FromSet s1) s1 z); [ reflexivity | exact Hz ].
Qed.

Lemma fd_names_spec B : FromSet (fd_names B) <--> name_in_fundefs B.
Proof.
  induction B; simpl.
  - rewrite FromSet_add, IHB. reflexivity.
  - rewrite FromSet_empty. reflexivity.
Qed.

Lemma strip_Hoist H Sset :
  (forall e acc e' acc', strip H e acc = (e', acc') -> hcheck H Sset e = true ->
     exists B n, Hoist (FromSet Sset) e e' B n /\ split_fds B acc acc') /\
  (forall B acc B' acc', strip_fds H B acc = (B', acc') -> hcheck_fds H Sset B = true ->
     exists Bc m, Hoist_keep (FromSet Sset) B B' Bc m /\ split_fds Bc acc acc').
Proof.
  eapply exp_def_mutual_ind.
  - intros x t ys e IH acc e' acc' Hs Hc. simpl in Hs, Hc.
    destruct (strip H e acc) as [e1 acc1] eqn:He. inv Hs.
    edestruct IH as [B [n [Hr Hsp]]]; [ exact He | exact Hc |]. eauto.
  - intros v acc e' acc' Hs Hc. simpl in Hs. inv Hs.
    exists Fnil, 0. split; [ constructor | eapply split_fds_nil_r ].
  - intros v l c e IHe IHl acc e' acc' Hs Hc. simpl in Hs, Hc. apply andb_prop in Hc as [Hc1 Hc2].
    destruct (strip H e acc) as [e1 acc1] eqn:He.
    match type of Hs with
    | context [ ?F l acc1 ] => destruct (F l acc1) as [cl acc2] eqn:Hl
    end.
    inv Hs.
    edestruct IHe as [B1 [n1 [Hr1 Hsp1]]]; [ exact He | exact Hc1 |].
    edestruct (IHl acc1) as [B2 [n2 [Hr2 Hsp2]]]; [ simpl; rewrite Hl; reflexivity | exact Hc2 |].
    destruct (split_compose _ _ _ _ _ Hsp1 Hsp2) as [Z [HZ1 HZ2]].
    exists Z, (max n2 n1). split; [| exact HZ2 ]. econstructor; [ exact Hr2 | exact Hr1 | exact HZ1 ].
  - intros x t n y e IH acc e' acc' Hs Hc. simpl in Hs, Hc.
    destruct (strip H e acc) as [e1 acc1] eqn:He. inv Hs.
    edestruct IH as [B [k [Hr Hsp]]]; [ exact He | exact Hc |]. eauto.
  - intros x f ft ys e IH acc e' acc' Hs Hc. simpl in Hs, Hc.
    destruct (strip H e acc) as [e1 acc1] eqn:He. inv Hs.
    edestruct IH as [B [n [Hr Hsp]]]; [ exact He | exact Hc |]. eauto.
  - intros B IHB e IHe acc e' acc' Hs Hc. simpl in Hs, Hc.
    apply andb_prop in Hc as [Hc Hce]. apply andb_prop in Hc as [Hch HcB].
    destruct (strip_fds H B acc) as [B' acc1] eqn:HB.
    destruct (strip H e acc1) as [e1 acc2] eqn:He.
    edestruct IHB as [Bb [m [HrB HspB]]]; [ exact HB | exact HcB |].
    edestruct IHe as [Be [n [Hre Hspe]]]; [ exact He | exact Hce |].
    destruct (split_compose _ _ _ _ _ HspB Hspe) as [Z [HZ1 HZ2]].
    destruct (hoisted H B); inv Hs.
    + exists (fundefs_append B' Z), (1 + max n m). split.
      * econstructor.
        -- rewrite fundefs_fv_correct. eapply subset_FromSet. exact Hch.
        -- exact Hre.
        -- eapply Hoist_keep_nested. exact HrB.
        -- eapply split_fds_append_r. exact HZ1.
      * eapply split_fds_append_l. exact HZ2.
    + exists Z, (max n m). split; [ econstructor; eassumption | exact HZ2 ].
  - intros f t ys acc e' acc' Hs Hc. simpl in Hs. inv Hs.
    exists Fnil, 0. split; [ constructor | eapply split_fds_nil_r ].
  - intros x p e IH acc e' acc' Hs Hc. simpl in Hs, Hc.
    destruct (strip H e acc) as [e1 acc1] eqn:He. inv Hs.
    edestruct IH as [B [n [Hr Hsp]]]; [ exact He | exact Hc |]. eauto.
  - intros x p ys e IH acc e' acc' Hs Hc. simpl in Hs, Hc.
    destruct (strip H e acc) as [e1 acc1] eqn:He. inv Hs.
    edestruct IH as [B [n [Hr Hsp]]]; [ exact He | exact Hc |]. eauto.
  - intros x acc e' acc' Hs Hc. simpl in Hs. inv Hs.
    exists Fnil, 0. split; [ constructor | eapply split_fds_nil_r ].
  - intros f t xs e IHe B IHB acc B' acc' Hs Hc. simpl in Hs, Hc. apply andb_prop in Hc as [Hce HcB].
    destruct (strip H e acc) as [e1 acc1] eqn:He.
    destruct (strip_fds H B acc1) as [B1 acc2] eqn:HB. inv Hs.
    edestruct IHe as [Bb [n [Hre Hspe]]]; [ exact He | exact Hce |].
    edestruct IHB as [Bk [m [HrB HspB]]]; [ exact HB | exact HcB |].
    destruct (split_compose _ _ _ _ _ Hspe HspB) as [Z [HZ1 HZ2]].
    exists Z, (max n m). split; [| exact HZ2 ].
    econstructor; [ exact Hre | exact HrB | eapply split_fds_sym; exact HZ1 ].
  - intros acc B' acc' Hs Hc. simpl in Hs. inv Hs.
    exists Fnil, 0. split; [ constructor | eapply split_fds_nil_r ].
Qed.

Scheme Hoist_ind3 := Induction for Hoist Sort Prop
  with Hoist_nested_ind3 := Induction for Hoist_nested Sort Prop
  with Hoist_keep_ind3 := Induction for Hoist_keep Sort Prop.
Combined Scheme Hoist_mut from Hoist_ind3, Hoist_nested_ind3, Hoist_keep_ind3.

Lemma Hoist_mon S S' :
  S \subset S' ->
  (forall e e' B n, Hoist S e e' B n -> Hoist S' e e' B n) /\
  (forall B B' n, Hoist_nested S B B' n -> Hoist_nested S' B B' n) /\
  (forall B B' Bc n, Hoist_keep S B B' Bc n -> Hoist_keep S' B B' Bc n).
Proof.
  intros Hs. apply Hoist_mut; intros; econstructor; eauto. eapply Included_trans; eassumption.
Qed.

(** * The top level *)

Section HoistTop.

  Variable (cenv : ctor_env).

  Lemma Hoist_top e e' B n :
    Hoist (name_in_fundefs B) e e' B n ->
    unique_bindings e -> Disjoint _ (bound_var e) (occurs_free e) ->
    forall k rho rho',
      preord_env_P cenv (hoisting_bound n n) (occurs_free e) k rho rho' ->
      preord_exp cenv (hoisting_bound n n) (hoisting_bound n n) k (e, rho) (Efun B e', rho').
  Proof.
    intros Hr Hun Hdis k rho rho' Henv.
    destruct (Hoist_unique _ _ _ _ _ Hr Hun) as [Hun1 [Hun2 Hd]].
    assert (Hbv := Hoist_bound_var _ _ _ _ _ Hr).
    eapply preord_exp_Efun_r.
    - eapply (hoisting_bound_compat cenv n n (le_n n)).
    - eapply (hoisting_bound_post_Efun_r n n). lia.
    - eapply (hoist_correct cenv n (fun i => hoisting_bound i n) (hoisting_bound n n))
        with (Bprev := Fnil) (B := B) (Ball := B); try eassumption.
      + intros i Hi. eapply hoisting_bound_compat. exact Hi.
      + intros i j Hij. eapply hoisting_bound_mon. exact Hij.
      + intros i. eapply hoisting_bound_post_Efun_l.
      + lia.
      + eapply preord_env_P_def_funs_not_in_P_r. eassumption.
        eapply Disjoint_Included_r; [| eapply Disjoint_sym; exact Hdis ].
        rewrite Hbv. eapply Included_trans; [ eapply name_in_fundefs_bound_var_fundefs | sets ].
      + eexists rho'. intros f Hfin. rewrite def_funs_eq. reflexivity. eassumption.
      + eapply split_fds_nil_r.
      + eapply Disjoint_Included_l; [ eapply name_in_fundefs_bound_var_fundefs | exact Hd ].
  Qed.

  Theorem hoist_top_correct e :
    unique_bindings e -> Disjoint _ (bound_var e) (occurs_free e) ->
    exists n,
      (forall k rho rho',
          preord_env_P cenv (hoisting_bound n n) (occurs_free e) k rho rho' ->
          preord_exp cenv (hoisting_bound n n) (hoisting_bound n n) k (e, rho) (hoist e, rho')) /\
      unique_bindings (hoist e) /\
      Disjoint _ (bound_var (hoist e)) (occurs_free (hoist e)) /\
      occurs_free (hoist e) \subset occurs_free e /\
      bound_var (hoist e) <--> bound_var e.
  Proof.
    intros Hun Hdis.
    assert (Hid : exists n,
               (forall k rho rho',
                   preord_env_P cenv (hoisting_bound n n) (occurs_free e) k rho rho' ->
                   preord_exp cenv (hoisting_bound n n) (hoisting_bound n n) k (e, rho) (e, rho')) /\
               unique_bindings e /\ Disjoint _ (bound_var e) (occurs_free e) /\
               occurs_free e \subset occurs_free e /\ bound_var e <--> bound_var e).
    { exists 0. split; [| split; [ exact Hun | split; [ exact Hdis | split; reflexivity ] ] ].
      intros k rho rho' Henv. eapply preord_exp_refl; [ eapply hoisting_bound_compat; lia | exact Henv ]. }
    unfold hoist.
    destruct (PS.is_empty _); [ exact Hid |].
    match goal with |- context [ strip ?H e Fnil ] =>
      destruct (strip H e Fnil) as [e1 Btop] eqn:Hs;
      destruct (hcheck H (fd_names Btop) e) eqn:Hc; simpl; [| exact Hid ];
      destruct (PS.subset _ _) eqn:Hsub; [| exact Hid ];
      destruct (proj1 (strip_Hoist H (fd_names Btop)) _ _ _ _ Hs Hc) as [B [n [Hr Hsp]]]
    end.
    apply split_fds_Fnil_eq_r in Hsp. subst B.
    apply (proj1 (Hoist_mon _ (name_in_fundefs Btop) (proj1 (fd_names_spec Btop)))) in Hr.
    destruct (Hoist_unique _ _ _ _ _ Hr Hun) as [Hun1 [Hun2 Hd]].
    assert (Hbv := Hoist_bound_var _ _ _ _ _ Hr).
    assert (Hfv : occurs_free (Efun Btop e1) \subset occurs_free e).
    { rewrite !exp_fv_correct. eapply subset_FromSet. exact Hsub. }
    assert (Hbv' : bound_var (Efun Btop e1) <--> bound_var e).
    { normalize_bound_var. rewrite Hbv. sets_ac. }
    exists n. split; [| split; [| split; [| split ] ] ].
    - intros k rho rho' Henv. eapply Hoist_top; eassumption.
    - constructor; [ exact Hun1 | exact Hun2 | eapply Disjoint_sym; exact Hd ].
    - rewrite Hbv'. eapply Disjoint_Included_r; [ exact Hfv | exact Hdis ].
    - exact Hfv.
    - exact Hbv'.
  Qed.

End HoistTop.
