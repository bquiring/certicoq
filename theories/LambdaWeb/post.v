(* Postconditions for λweb.

   CertiRocq's logical relations carry a local postcondition [P] and a
   global postcondition [PG] relating the fuel consumed and the traces
   produced by the two executions.  The compatibility lemmas require the
   postconditions to be closed under the evaluation rules; these are the
   λweb versions of the side conditions of LambdaANF/logical_relations.v
   ([post_constr_compat], ..., [Post_properties]). *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Relations.Relations micromega.Lia.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import algebra List_util.
From CertiRocq.LambdaWeb Require Import syntax semantics exposed.

Import ListNotations.

Open Scope alg_scope.

(** * Fuel ordering *)

Section Ge.

  Context {I A : Type} {HR : @resource I A}.

  Definition ge (x y : A) : Prop := exists c, x = (c <+> y).

  Lemma ge_refl x : ge x x.
  Proof. exists zero. rewrite plus_zero. reflexivity. Qed.

  Lemma ge_trans x y z : ge x y -> ge y z -> ge x z.
  Proof. intros [a Ha] [b Hb]. subst. exists (a <+> b). rewrite plus_assoc. reflexivity. Qed.

  Lemma ge_plus_l x y : ge (y <+> x) x.
  Proof. exists y. reflexivity. Qed.

  Lemma ge_plus_r x y : ge (x <+> y) x.
  Proof. exists y. apply plus_comm. Qed.

  Lemma ge_add x y x' y' : ge x y -> ge x' y' -> ge (x <+> x') (y <+> y').
  Proof.
    intros [a Ha] [b Hb]. subst. exists (a <+> b).
    rewrite !plus_assoc. f_equal. rewrite <- !plus_assoc. f_equal. apply plus_comm.
  Qed.

End Ge.

Section Post.

  Variable (cenv : term.ctor_env).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Local Notation PostT := (@exposed.PostT fuel trace).
  Local Notation PostGT := (@exposed.PostGT fuel trace).

  (** Versions of the properties where the expressions and environments
      are externalized *)

  Definition post_constr_compat' x w t ys e1 rho1 x' w' t' ys' e2 rho2 (P1 P2 : PostT) :=
    forall vs vs' c1 c2 cout1 cout2,
      get_list ys rho1 = Some vs ->
      get_list ys' rho2 = Some vs' ->
      P1 (e1, M.set x (Vconstr w t vs) rho1, c1, cout1) (e2, M.set x' (Vconstr w' t' vs') rho2, c2, cout2) ->
      P2 (Econstr x w t ys e1, rho1, c1 <+> one_w (Econstr x w t ys e1), cout1 <+> one_w (Econstr x w t ys e1))
         (Econstr x' w' t' ys' e2, rho2, c2 <+> one_w (Econstr x' w' t' ys' e2), cout2 <+> one_w (Econstr x' w' t' ys' e2)).

  Definition post_proj_compat' x w t N y e1 rho1 x' w' t' N' y' e2 rho2 (P1 P2 : PostT) :=
    forall vs v1 v2 c1 c2 cout1 cout2,
      M.get y rho1 = Some (Vconstr w t vs) ->
      nthN vs N = Some v1 ->
      P1 (e1, M.set x v1 rho1, c1, cout1) (e2, M.set x' v2 rho2, c2, cout2) ->
      P2 (Eproj x w t N y e1, rho1, c1 <+> one_w (Eproj x w t N y e1), cout1 <+> one_w (Eproj x w t N y e1))
         (Eproj x' w' t' N' y' e2, rho2, c2 <+> one_w (Eproj x' w' t' N' y' e2), cout2 <+> one_w (Eproj x' w' t' N' y' e2)).

  Definition post_case_compat_hd' x w t e1 B1 rho1 x' w' t' e2 B2 rho2 (P1 P2 : PostT) :=
    forall c1 c2 cout1 cout2,
      P1 (e1, rho1, c1, cout1) (e2, rho2, c2, cout2) ->
      P2 (Ecase x w ((t, e1) :: B1), rho1, c1 <+> one_w (Ecase x w ((t, e1) :: B1)), cout1 <+> one_w (Ecase x w ((t, e1) :: B1)))
         (Ecase x' w' ((t', e2) :: B2), rho2, c2 <+> one_w (Ecase x' w' ((t', e2) :: B2)), cout2 <+> one_w (Ecase x' w' ((t', e2) :: B2))).

  Definition post_case_compat_tl' x w t e1 B1 rho1 x' w' t' e2 B2 rho2 (P1 P2 : PostT) :=
    forall c1 c2 cout1 cout2,
      P1 (Ecase x w B1, rho1, c1, cout1) (Ecase x' w' B2, rho2, c2, cout2) ->
      P2 (Ecase x w ((t, e1) :: B1), rho1, c1, cout1) (Ecase x' w' ((t', e2) :: B2), rho2, c2, cout2).

  Definition post_fun_compat' B1 e1 rho1 B2 e2 rho2 (P1 P2 : PostT) :=
    forall c1 c2 cout1 cout2,
      P1 (e1, def_funs B1 B1 rho1 rho1, c1, cout1) (e2, def_funs B2 B2 rho2 rho2, c2, cout2) ->
      P2 (Efun B1 e1, rho1, c1 <+> one_w (Efun B1 e1), cout1 <+> one_w (Efun B1 e1))
         (Efun B2 e2, rho2, c2 <+> one_w (Efun B2 e2), cout2 <+> one_w (Efun B2 e2)).

  Definition post_OOT' e1 rho1 e2 rho2 (P1 : PostT) :=
    forall c,
      c << one_w e1 -> P1 (e1, rho1, c, <0>) (e2, rho2, c, <0>).

  Definition post_base' x rho1 y rho2 (P1 : PostT) :=
    P1 (Ehalt x, rho1, one_w (Ehalt x), one_w (Ehalt x)) (Ehalt y, rho2, one_w (Ehalt y), one_w (Ehalt y)).

  Definition post_app_compat' f w ys rho1 f' w' ys' rho2 (P : PostT) (PG : PostGT) :=
    forall xs e1 e2 rhoc1 rhoc2 B h vs rhoc1' c1 c2 cout1 cout2,
      M.get f rho1 = Some (Vfun rhoc1 B h) ->
      get_list ys rho1 = Some vs ->
      find_def h B = Some (w, xs, e1) ->
      set_lists xs vs (def_funs B B rhoc1 rhoc1) = Some rhoc1' ->
      PG (e1, rhoc1', c1, cout1) (e2, rhoc2, c2, cout2) ->
      P (Eapp f w ys, rho1, c1 <+> one_w (Eapp f w ys), cout1 <+> one_w (Eapp f w ys))
        (Eapp f' w' ys', rho2, c2 <+> one_w (Eapp f' w' ys'), cout2 <+> one_w (Eapp f' w' ys')).

  Definition post_letapp_compat' x f w ys e1 rho1 x' f' w' ys' e2 rho2 (P1 P2 : PostT) (PG : PostGT) :=
    forall xs e_b1 v1 e_b2 v2
           rhoc1 rhoc2 B h vs rhoc1' c1 c1' c2 c2' cout1 cout2 cout1' cout2',
      M.get f rho1 = Some (Vfun rhoc1 B h) ->
      get_list ys rho1 = Some vs ->
      find_def h B = Some (w, xs, e_b1) ->
      set_lists xs vs (def_funs B B rhoc1 rhoc1) = Some rhoc1' ->
      bstep_fuel cenv (exposedb w) rhoc1' e_b1 c1 (Res v1) cout1 ->
      PG (e_b1, rhoc1', c1, cout1) (e_b2, rhoc2, c2, cout2) ->
      P1 (e1, M.set x v1 rho1, c1', cout1') (e2, M.set x' v2 rho2, c2', cout2') ->
      P2 (Eletapp x f w ys e1, rho1, c1 <+> c1' <+> one_w (Eletapp x f w ys e1), cout1 <+> cout1' <+> one_w (Eletapp x f w ys e1))
         (Eletapp x' f' w' ys' e2, rho2, c2 <+> c2' <+> one_w (Eletapp x' f' w' ys' e2), cout2 <+> cout2' <+> one_w (Eletapp x' f' w' ys' e2)).

  Definition post_letapp_compat_OOT' x f w ys e1 rho1 x' f' w' ys' e2 rho2 (P2 : PostT) (PG : PostGT) :=
    forall xs e_b1 e_b2 rhoc1 rhoc2 B h vs rhoc1' c1 c2 cout1 cout2,
      M.get f rho1 = Some (Vfun rhoc1 B h) ->
      get_list ys rho1 = Some vs ->
      find_def h B = Some (w, xs, e_b1) ->
      set_lists xs vs (def_funs B B rhoc1 rhoc1) = Some rhoc1' ->
      PG (e_b1, rhoc1', c1, cout1) (e_b2, rhoc2, c2, cout2) ->
      P2 (Eletapp x f w ys e1, rho1, c1 <+> one_w (Eletapp x f w ys e1), cout1 <+> one_w (Eletapp x f w ys e1))
         (Eletapp x' f' w' ys' e2, rho2, c2 <+> one_w (Eletapp x' f' w' ys' e2), cout2 <+> one_w (Eletapp x' f' w' ys' e2)).

  (** Properties over all expressions and environments *)

  Definition post_constr_compat (P1 P2 : PostT) :=
    forall x w t ys e1 rho1 x' w' t' ys' e2 rho2, post_constr_compat' x w t ys e1 rho1 x' w' t' ys' e2 rho2 P1 P2.

  Definition post_proj_compat (P1 P2 : PostT) :=
    forall x w t N y e1 rho1 x' w' t' N' y' e2 rho2, post_proj_compat' x w t N y e1 rho1 x' w' t' N' y' e2 rho2 P1 P2.

  Definition post_case_compat_hd (P1 P2 : PostT) :=
    forall x w t e1 B1 rho1 x' w' t' e2 B2 rho2, post_case_compat_hd' x w t e1 B1 rho1 x' w' t' e2 B2 rho2 P1 P2.

  Definition post_case_compat_tl (P1 P2 : PostT) :=
    forall x w t e1 B1 rho1 x' w' t' e2 B2 rho2, post_case_compat_tl' x w t e1 B1 rho1 x' w' t' e2 B2 rho2 P1 P2.

  Definition post_fun_compat (P1 P2 : PostT) :=
    forall B1 e1 rho1 B2 e2 rho2, post_fun_compat' B1 e1 rho1 B2 e2 rho2 P1 P2.

  Definition post_OOT (P1 : PostT) :=
    forall e1 rho1 e2 rho2, post_OOT' e1 rho1 e2 rho2 P1.

  Definition post_base (P1 : PostT) :=
    forall x rho1 y rho2, post_base' x rho1 y rho2 P1.

  Definition post_app_compat (P : PostT) (PG : PostGT) :=
    forall f w ys rho1 f' w' ys' rho2, post_app_compat' f w ys rho1 f' w' ys' rho2 P PG.

  Definition post_letapp_compat (P1 P2 : PostT) (PG : PostGT) :=
    forall x f w ys e1 rho1 x' f' w' ys' e2 rho2, post_letapp_compat' x f w ys e1 rho1 x' f' w' ys' e2 rho2 P1 P2 PG.

  Definition post_letapp_compat_OOT (P2 : PostT) (PG : PostGT) :=
    forall x f w ys e1 rho1 x' f' w' ys' e2 rho2, post_letapp_compat_OOT' x f w ys e1 rho1 x' f' w' ys' e2 rho2 P2 PG.

  Class Post_properties (P1 P2 : PostT) (PG : PostGT) : Prop :=
    { HPost_con : post_constr_compat P1 P2;
      HPost_proj : post_proj_compat P1 P2;
      HPost_fun : post_fun_compat P1 P2;
      HPost_case_hd : post_case_compat_hd P1 P2;
      HPost_case_tl : post_case_compat_tl P2 P2;
      HPost_app : post_app_compat P1 PG;
      HPost_letapp : post_letapp_compat P1 P2 PG;
      HPost_letapp_OOT : post_letapp_compat_OOT P1 PG;
      HPost_OOT : post_OOT P2;
      Hpost_base : post_base P2;
      HGPost : inclusion _ P1 PG }.

  (** Upper bound on the fuel consumed by the target; this is what gives
      divergence preservation. *)
  Definition post_upper_bound (P : PostT) :=
    forall e1 rho1 e2 rho2,
    exists (f : fuel -> fuel),
    forall cin1 cin2 cout1 cout2,
      P (e1, rho1, f cin1, cout1) (e2, rho2, cin2, cout2) ->
      exists (c : fuel), cin2 = (c <+> cin1).

  (** The trivial postcondition satisfies all compatibility conditions. *)
  Definition post_true : PostT := fun _ _ => True.

  Global Instance Post_properties_true : Post_properties post_true post_true post_true.
  Proof. constructor; unfold post_true; repeat intro; exact I. Qed.

  Lemma one_w_eq (e1 e2 : exp) : (one_w e1 : fuel) = one_w e2.
  Proof. unfold one_w, algebra.one. apply one_eq. Qed.

  (** ** Postconditions insensitive to extra target steps *)

  Definition post_target_steps (P : PostT) :=
    forall e1 rho1 c1 t1 e2 rho2 c2 t2 e2' rho2' c2' t2',
      P (e1, rho1, c1, t1) (e2, rho2, c2, t2) -> ge c2' c2 ->
      P (e1, rho1, c1, t1) (e2', rho2', c2', t2').

  (** The target uses at least as much fuel as the source *)
  Definition P_ge : PostT :=
    fun p1 p2 => match p1, p2 with (_, _, c1, _), (_, _, c2, _) => ge c2 c1 end.

  Lemma P_ge_target_steps : post_target_steps P_ge.
  Proof. intros until t2'. simpl. intros H Hc. eapply ge_trans; eauto. Qed.

  Lemma P_ge_upper_bound : post_upper_bound P_ge.
  Proof. intros e1 rho1 e2 rho2. exists (fun c => c). intros cin1 cin2 cout1 cout2 H. exact H. Qed.

  Global Instance P_ge_properties : Post_properties P_ge P_ge P_ge.
  Proof.
    constructor; repeat intro; simpl in *;
      repeat match goal with
             | [ H : P_ge _ _ |- _ ] => simpl in H
             end.
    - erewrite (one_w_eq (Econstr _ _ _ _ e2)). eapply ge_add; eauto. eapply ge_refl.
    - erewrite (one_w_eq (Eproj _ _ _ _ _ e2)). eapply ge_add; eauto. eapply ge_refl.
    - erewrite (one_w_eq (Efun B2 e2)). eapply ge_add; eauto. eapply ge_refl.
    - erewrite (one_w_eq (Ecase _ _ ((_, e2) :: _))). eapply ge_add; eauto. eapply ge_refl.
    - eauto.
    - erewrite (one_w_eq (Eapp _ _ _)). eapply ge_add; eauto. eapply ge_refl.
    - erewrite (one_w_eq (Eletapp _ _ _ _ e2)). eapply ge_add; [ eapply ge_add |]; eauto. eapply ge_refl.
    - erewrite (one_w_eq (Eletapp _ _ _ _ e2)). eapply ge_add; eauto. eapply ge_refl.
    - eapply ge_refl.
    - unfold post_base'. simpl. rewrite (one_w_eq (Ehalt y) (Ehalt x)). apply ge_refl.
    - assumption.
  Qed.


  (** ** Postconditions for removed and added binding steps *)

  (** Binding forms that dead-binding elimination removes and constant
      propagation inserts.  They are not calls. *)
  Definition binding_step (e : exp) : Prop :=
    match e with
    | Econstr _ _ _ _ _ | Eproj _ _ _ _ _ _ | Efun _ _ => True
    | _ => False
    end.

  (** A binding step taken only by the source. *)
  Definition post_source_step (P1 P2 : PostT) :=
    forall e1 rho1 e1' rho1' e2 rho2 c1 t1 c2 t2,
      binding_step e1 ->
      P1 (e1', rho1', c1, t1) (e2, rho2, c2, t2) ->
      P2 (e1, rho1, c1 <+> one_w e1, t1 <+> one_w e1) (e2, rho2, c2, t2).

  (** A binding step taken only by the target. *)
  Definition post_target_step (P : PostT) :=
    forall e1 rho1 c1 t1 e2 rho2 e2' rho2' c2 t2,
      binding_step e2' ->
      P (e1, rho1, c1, t1) (e2, rho2, c2, t2) ->
      P (e1, rho1, c1, t1) (e2', rho2', c2 <+> one_w e2', t2 <+> one_w e2').

  (** A family of postconditions indexed by the number of source binding
      steps that may be removed on the current path (between calls); [Gb]
      bounds it, and function bodies are checked at [Gb].  This is the
      structure of CertiRocq's [inline_bound L G] (LambdaANF/bounds.v). *)
  Class Post_dead (P : nat -> PostT) (PG : PostGT) (Gb : nat) : Prop :=
    { Hdead_props : forall n : nat, (n <= Gb)%nat -> Post_properties (P n) (P n) PG;
      Hdead_mono : forall n m : nat, (n <= m)%nat -> (m <= Gb)%nat -> inclusion _ (P n) (P m);
      Hdead_src : forall n : nat, (n < Gb)%nat -> post_source_step (P n) (P (S n)) }.

  (** Any postcondition, when no step is removed. *)
  Global Instance Post_dead_const P PG {Hp : Post_properties P P PG} :
    Post_dead (fun _ => P) PG 0.
  Proof.
    constructor.
    - intros; assumption.
    - intros n m _ _ x y H; exact H.
    - intros n Hn. lia.
  Qed.

End Post.
