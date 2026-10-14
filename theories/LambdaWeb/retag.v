(* Erasure for the compiler: function tags for internal webs.

   [erase] maps a web to its index, so an internal web [Internal p] becomes
   the λANF function tag [p].  The compiler's function environment does not
   know these tags, they may clash with existing tags, and functions of
   different arities may share a web.  [erase_rt] instead gives each pair of
   an internal web and an arity a fresh function tag, and records its arity
   in the function environment.  Exposed webs keep their λANF tag.

   A call and the functions it may call share a web, and a call only
   succeeds on a function of its arity, so the tags still agree wherever a
   call succeeds. *)

From Stdlib Require Import NArith.BinNat Lists.List.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import List_util.
From CertiRocq.LambdaANF Require term.
From CertiRocq.LambdaWeb Require Import syntax.

Import ListNotations.

Record rt_st : Type :=
  mk_rt { rt_map : M.t (list (nat * term.fun_tag));  (* tags of an internal web, by arity *)
          rt_next : term.fun_tag;                     (* the next fresh function tag *)
          rt_fenv : term.fun_env }.

Definition rt_tag (w : web) (n : nat) (s : rt_st) : term.fun_tag * rt_st :=
  match w with
  | Exposed t => (t, s)
  | Internal p =>
      let l := match M.get p (rt_map s) with Some l => l | None => [] end in
      match List.find (fun q => Nat.eqb (fst q) n) l with
      | Some (_, t) => (t, s)
      | None =>
          let t := rt_next s in
          (t, mk_rt (M.set p ((n, t) :: l) (rt_map s)) (Pos.succ t)
                    (M.set t (N.of_nat n, fromN 0%N n) (rt_fenv s)))
      end
  end.

Fixpoint erase_rt (e : exp) (s : rt_st) : term.exp * rt_st :=
  match e with
  | Econstr x w t ys e => let '(e, s) := erase_rt e s in (term.Econstr x t ys e, s)
  | Ecase x w cl =>
      let '(cl, s) :=
        (fix erase_br (cl : list (ctor_tag * exp)) (s : rt_st) :=
           match cl with
           | [] => ([], s)
           | (c, e) :: cl =>
               let '(e, s) := erase_rt e s in
               let '(cl, s) := erase_br cl s in
               ((c, e) :: cl, s)
           end) cl s in
      (term.Ecase x cl, s)
  | Eproj x w t n y e => let '(e, s) := erase_rt e s in (term.Eproj x t n y e, s)
  | Eletapp x f w ys e =>
      let '(t, s) := rt_tag w (length ys) s in
      let '(e, s) := erase_rt e s in
      (term.Eletapp x f t ys e, s)
  | Efun B e =>
      let '(B, s) := erase_rt_fds B s in
      let '(e, s) := erase_rt e s in
      (term.Efun B e, s)
  | Eapp f w ys => let '(t, s) := rt_tag w (length ys) s in (term.Eapp f t ys, s)
  | Eprim_val x p e => let '(e, s) := erase_rt e s in (term.Eprim_val x p e, s)
  | Eprim x p ys e => let '(e, s) := erase_rt e s in (term.Eprim x p ys e, s)
  | Ehalt x => (term.Ehalt x, s)
  end
with erase_rt_fds (B : fundefs) (s : rt_st) : term.fundefs * rt_st :=
  match B with
  | Fcons f w xs e B =>
      let '(t, s) := rt_tag w (length xs) s in
      let '(e, s) := erase_rt e s in
      let '(B, s) := erase_rt_fds B s in
      (term.Fcons f t xs e B, s)
  | Fnil => (term.Fnil, s)
  end.

(** * [erase_rt] is erasure with a tag function *)

From CertiRocq.LambdaWeb Require Import erase.

Definition rt_lookup (m : M.t (list (nat * term.fun_tag))) (p : positive) (n : nat) : option term.fun_tag :=
  match M.get p m with
  | Some l => match List.find (fun q => Nat.eqb (fst q) n) l with Some (_, t) => Some t | None => None end
  | None => None
  end.

(** The tags of a table: exposed webs keep their λANF tag *)
Definition tagf_of (s : rt_st) (w : web) (n : nat) : term.fun_tag :=
  match w with
  | Exposed t => t
  | Internal p => match rt_lookup (rt_map s) p n with Some t => t | None => 1%positive end
  end.

Definition rt_ext (s s' : rt_st) : Prop :=
  forall p n t, rt_lookup (rt_map s) p n = Some t -> rt_lookup (rt_map s') p n = Some t.

(** A tag function agrees with a table *)
Definition agrees (tagf : web -> nat -> term.fun_tag) (s : rt_st) : Prop :=
  (forall t n, tagf (Exposed t) n = t) /\
  (forall p n t, rt_lookup (rt_map s) p n = Some t -> tagf (Internal p) n = t).

Lemma rt_ext_refl s : rt_ext s s.
Proof. intros p n t H; exact H. Qed.

Lemma rt_ext_trans s1 s2 s3 : rt_ext s1 s2 -> rt_ext s2 s3 -> rt_ext s1 s3.
Proof. intros H1 H2 p n t H. eauto. Qed.

Lemma agrees_ext tagf s s' : rt_ext s s' -> agrees tagf s' -> agrees tagf s.
Proof. intros Hx [H1 H2]. split; [ exact H1 | intros; eapply H2; eauto ]. Qed.

Lemma rt_tag_spec w n s :
  rt_ext s (snd (rt_tag w n s)) /\
  (forall tagf, agrees tagf (snd (rt_tag w n s)) -> tagf w n = fst (rt_tag w n s)).
Proof.
  destruct w as [t | p]; simpl.
  - split; [ eapply rt_ext_refl | intros tagf [H1 _]; eapply H1 ].
  - destruct (M.get p (rt_map s)) as [l |] eqn:Hp;
      destruct (List.find (fun q => Nat.eqb (fst q) n) l) as [[n' t] |] eqn:Hf || idtac.
    + simpl. split; [ eapply rt_ext_refl |].
      intros tagf [_ H2]. eapply H2. unfold rt_lookup. rewrite Hp, Hf. reflexivity.
    + simpl. split.
      * intros p' n'' t' Hl. unfold rt_lookup in *. simpl. rewrite M.gsspec.
        destruct (peq p' p); [ subst | exact Hl ]. rewrite Hp in Hl. simpl.
        destruct (Nat.eqb n n'') eqn:Hn; [| exact Hl ].
        apply Nat.eqb_eq in Hn. subst. rewrite Hf in Hl. discriminate.
      * intros tagf [_ H2]. eapply H2. unfold rt_lookup. simpl. rewrite M.gss. simpl.
        rewrite Nat.eqb_refl. reflexivity.
    + simpl. split.
      * intros p' n'' t' Hl. unfold rt_lookup in *. simpl. rewrite M.gsspec.
        destruct (peq p' p); [ subst; rewrite Hp in Hl; discriminate | exact Hl ].
      * intros tagf [_ H2]. eapply H2. unfold rt_lookup. simpl. rewrite M.gss. simpl.
        rewrite Nat.eqb_refl. reflexivity.
Qed.

Ltac rt_step H :=
  match goal with
  | |- context [ rt_tag ?w ?n ?s ] =>
      let Ht := fresh "Ht" in let Hs := fresh "Hs" in
      destruct (rt_tag_spec w n s) as [Ht Hs];
      destruct (rt_tag w n s) as [?t ?s] eqn:H; simpl in Ht, Hs
  end.

Lemma erase_rt_spec :
  (forall e s, rt_ext s (snd (erase_rt e s)) /\
               forall tagf, agrees tagf (snd (erase_rt e s)) -> fst (erase_rt e s) = erase_t tagf e) /\
  (forall B s, rt_ext s (snd (erase_rt_fds B s)) /\
               forall tagf, agrees tagf (snd (erase_rt_fds B s)) -> fst (erase_rt_fds B s) = erase_t_fundefs tagf B).
Proof.
  eapply exp_fundefs_ind; intros; simpl.
  - destruct (H s) as [H1 H2]. destruct (erase_rt e s) as [e' s'] eqn:He; simpl in *.
    split; [ exact H1 | intros; f_equal; eauto ].
  - split; [ eapply rt_ext_refl | reflexivity ].
  - destruct (H s) as [H1 H2]. destruct (erase_rt e s) as [e' s1] eqn:He; simpl in *.
    destruct (H0 s1) as [H3 H4]. simpl in H3, H4.
    match goal with |- context [ ?F cl s1 ] => destruct (F cl s1) as [cl' s2] eqn:Hcl end.
    simpl in *. split; [ eapply rt_ext_trans; eauto |].
    intros tagf Hag. specialize (H4 tagf Hag). inv H4.
    rewrite (H2 tagf (agrees_ext _ _ _ H3 Hag)). reflexivity.
  - destruct (H s) as [H1 H2]. destruct (erase_rt e s) as [e' s'] eqn:He; simpl in *.
    split; [ exact H1 | intros; f_equal; eauto ].
  - rt_step Hr. destruct (H s0) as [H1 H2]. destruct (erase_rt e s0) as [e' s1] eqn:He; simpl in *.
    split; [ eapply rt_ext_trans; eauto |].
    intros tagf Hag. rewrite (Hs tagf (agrees_ext _ _ _ H1 Hag)), (H2 tagf Hag). reflexivity.
  - destruct (H s) as [H1 H2]. destruct (erase_rt_fds B s) as [B' s1] eqn:HB; simpl in *.
    destruct (H0 s1) as [H3 H4]. destruct (erase_rt e s1) as [e' s2] eqn:He; simpl in *.
    split; [ eapply rt_ext_trans; eauto |].
    intros tagf Hag. rewrite (H2 tagf (agrees_ext _ _ _ H3 Hag)), (H4 tagf Hag). reflexivity.
  - rt_step Hr. split; [ exact Ht | intros tagf Hag; rewrite (Hs tagf Hag); reflexivity ].
  - destruct (H s) as [H1 H2]. destruct (erase_rt e s) as [e' s'] eqn:He; simpl in *.
    split; [ exact H1 | intros; f_equal; eauto ].
  - destruct (H s) as [H1 H2]. destruct (erase_rt e s) as [e' s'] eqn:He; simpl in *.
    split; [ exact H1 | intros; f_equal; eauto ].
  - split; [ eapply rt_ext_refl | reflexivity ].
  - rt_step Hr. destruct (H s0) as [H1 H2]. destruct (erase_rt e s0) as [e' s1] eqn:He; simpl in *.
    destruct (H0 s1) as [H3 H4]. destruct (erase_rt_fds B s1) as [B' s2] eqn:HB; simpl in *.
    split; [ eapply rt_ext_trans; [ eassumption | eapply rt_ext_trans; eassumption ] |].
    intros tagf Hag.
    rewrite (Hs tagf (agrees_ext _ _ _ (rt_ext_trans _ _ _ H1 H3) Hag)),
            (H2 tagf (agrees_ext _ _ _ H3 Hag)), (H4 tagf Hag). reflexivity.
  - split; [ eapply rt_ext_refl | reflexivity ].
Qed.

Lemma agrees_tagf_of s : agrees (tagf_of s) s.
Proof.
  split; [ reflexivity |]. intros p n t H. simpl. rewrite H. reflexivity.
Qed.

(** [erase_rt] computes erasure with the tags of its final table. *)
Theorem erase_rt_erase_t e s :
  fst (erase_rt e s) = erase_t (tagf_of (snd (erase_rt e s))) e.
Proof. eapply (proj1 erase_rt_spec). eapply agrees_tagf_of. Qed.
