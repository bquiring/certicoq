(* An implementation of the 0-CFA: a solver, the annotation it induces, and
   a checker of the constraints proven sound.

   The solver is not verified.  It iterates a pass over the program that
   propagates flows, exposure (escape) and the arguments and results of
   functions until nothing changes, then merges the internal webs of the
   labels that share a use site.  The checker decides [ok_top] for the
   annotation of the solution; when it fails, the analysis falls back to
   the trivial solution, in which every value is exposed.  So [annotate]
   always inhabits the annotation relation ([annotate_correct]). *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics set_util algebra.
From CertiRocq.LambdaANF Require term identifiers.
From CertiRocq.LambdaWeb Require Import syntax anno.
From CertiRocq.LambdaCFA Require Import spec sound.

From Stdlib Require Import SetoidList.
Import ListNotations.

(** * Sets *)

Definition ain_b (l : lab) (A : aset) : bool :=
  match A with AFin a => PS.mem l a | AAll => true end.

Lemma ain_b_spec l A : ain_b l A = true <-> ain l A.
Proof. destruct A; simpl; [ eapply PS.mem_spec | tauto ]. Qed.

Definition sub_b (A B : aset) : bool :=
  match A, B with
  | _, AAll => true
  | AFin a, AFin b => PS.subset a b
  | AAll, AFin _ => false
  end.

Lemma sub_b_spec A B : sub_b A B = true -> sub A B.
Proof.
  destruct A, B; simpl; intros H l Hl; simpl in *; try easy.
  eapply PS.subset_spec in H. eauto.
Qed.

Lemma In_elements l a : PS.In l a -> List.In l (PS.elements a).
Proof.
  intros H. eapply PS.elements_spec1 in H. eapply InA_alt in H.
  destruct H as (y & Heq & Hy). subst. exact Hy.
Qed.

Lemma forallb_elements (P : lab -> bool) a :
  forallb P (PS.elements a) = true -> forall l, PS.In l a -> P l = true.
Proof. intros H l Hl. eapply forallb_forall in H; eauto. eapply In_elements; eauto. Qed.

(** Iterating over a map with a default *)
Definition all_map {A} (p : A -> bool) (m : M.t A) (d : A) : bool :=
  p d && forallb (fun '(_, a) => p a) (M.elements m).

Lemma all_map_spec {A} p (m : M.t A) d : all_map p m d = true -> forall k, p (getd m d k) = true.
Proof.
  unfold all_map, getd. intros H k. eapply andb_prop in H. destruct H as [Hd Hm].
  destruct (M.get k m) as [a |] eqn:Hk; eauto.
  eapply M.elements_correct in Hk. eapply forallb_forall in Hm; [| exact Hk ]. exact Hm.
Qed.

(** Iterating over a map of lists with a default, at every position *)
Definition all_lists {A} (p : A -> bool) (m : M.t (list A)) (d : A) : bool :=
  p d && forallb (fun '(_, l) => forallb p l) (M.elements m).

Lemma all_lists_spec {A} p (m : M.t (list A)) d :
  all_lists p m d = true -> forall k i, p (nth i (getd m [] k) d) = true.
Proof.
  unfold all_lists, getd. intros H k i. eapply andb_prop in H. destruct H as [Hd Hm].
  destruct (nth_in_or_default i (match M.get k m with Some a => a | None => [] end) d) as [Hin | Heq];
    [| rewrite Heq; exact Hd ].
  destruct (M.get k m) as [l |] eqn:Hk; [| destruct i; inv Hin ].
  eapply M.elements_correct in Hk. eapply forallb_forall in Hm; [| exact Hk ].
  eapply forallb_forall in Hm; eauto.
Qed.

Fixpoint forall_i {A} (p : nat -> A -> bool) (i : nat) (l : list A) : bool :=
  match l with
  | [] => true
  | a :: l => p i a && forall_i p (S i) l
  end.

Lemma forall_i_spec {A} p (l : list A) n :
  forall_i p n l = true -> forall i a, nth_error l i = Some a -> p (n + i) a = true.
Proof.
  revert n; induction l; intros n H [| i] b Hn; simpl in *; try congruence.
  - inv Hn. eapply andb_prop in H. replace (n + 0) with n by lia. apply H.
  - eapply andb_prop in H. replace (n + S i) with (S n + i) by lia. eapply IHl; eauto. apply H.
Qed.

Definition is_flab (l : lab) : bool := match l with xO _ => true | _ => false end.
Definition is_clab (l : lab) : bool := match l with xI _ => true | _ => false end.

Section Check.

  Variable (w_con : web).
  Hypothesis (Hw_con : exposedb w_con = true).
  Variable (s : sol).

  Local Notation fl := (fl s).
  Local Notation Arg := (Arg s).
  Local Notation Fld := (Fld s).
  Local Notation Ret := (Ret s).
  Local Notation wfun := (wfun s).
  Local Notation wcon := (wcon w_con s).

  Definition all_ex : bool := match s_ex s with AAll => true | AFin _ => false end.

  Lemma all_ex_spec : all_ex = true -> forall l, ain l (s_ex s).
  Proof. unfold all_ex. destruct (s_ex s); easy. Qed.

  Lemma all_ex_isex : all_ex = true -> forall l, isex s l = true.
  Proof. unfold all_ex, isex. destruct (s_ex s); easy. Qed.

  Definition esc_b (A : aset) : bool :=
    match A with
    | AFin a => forallb (fun l => Pos.eqb l ltop || isex s l) (PS.elements a)
    | AAll => all_ex
    end.

  Lemma esc_b_spec A : esc_b A = true -> esc s A.
  Proof.
    destruct A; simpl; intros H l Hl.
    - eapply forallb_elements in H; eauto. eapply orb_prop in H as [H | H].
      + left. now eapply Peqb_true_eq.
      + right. now eapply isex_ain.
    - right. eapply all_ex_spec; eauto.
  Qed.

  (** ** The annotation induced by a solution *)

  (** The web of a use site of [y] (projection, case) *)
  Definition wuse (y : var) : web :=
    if ain_b ltop (fl y) then w_con else
      match fl y with
      | AFin a =>
          match List.find is_clab (PS.elements a) with
          | Some (xI z) => wcon z
          | _ => w_con
          end
      | AAll => w_con
      end.

  (** The web of a call site of [f] at λANF tag [t] *)
  Definition wapp (f : var) (t : term.fun_tag) : web :=
    if ain_b ltop (fl f) then Exposed t else
      match fl f with
      | AFin a =>
          match List.find is_flab (PS.elements a) with
          | Some (xO g) => wfun g t
          | _ => Exposed t
          end
      | AAll => Exposed t
      end.

  Fixpoint anno (e : term.exp) : exp :=
    match e with
    | term.Econstr x c ys e => Econstr x (wcon x) c ys (anno e)
    | term.Ecase y cl =>
        Ecase y (wuse y)
              ((fix anno_br (cl : list (term.ctor_tag * term.exp)) :=
                  match cl with
                  | [] => []
                  | (c, e) :: cl => (c, anno e) :: anno_br cl
                  end) cl)
    | term.Eproj x c n y e => Eproj x (wuse y) c n y (anno e)
    | term.Eletapp x f t ys e => Eletapp x f (wapp f t) ys (anno e)
    | term.Efun B e => Efun (anno_fds B) (anno e)
    | term.Eapp f t ys => Eapp f (wapp f t) ys
    | term.Eprim_val x p e => Eprim_val x p (anno e)
    | term.Eprim x p ys e => Eprim x p ys (anno e)
    | term.Ehalt x => Ehalt x
    end
  with anno_fds (B : term.fundefs) : fundefs :=
    match B with
    | term.Fcons g t xs b B => Fcons g (wfun g t) xs (anno b) (anno_fds B)
    | term.Fnil => Fnil
    end.

  (** ** The checker *)

  Definition use_b (y : var) (w : web) : bool :=
    match fl y with
    | AFin a =>
        forallb (fun l => match l with
                          | xI z => web_eqb (wcon z) w
                          | xH => web_eqb w w_con
                          | _ => true
                          end) (PS.elements a)
    | AAll => all_ex && web_eqb w w_con
    end.

  Lemma use_b_spec y w : use_b y w = true -> use_ok w_con s y w.
  Proof.
    unfold use_b, use_ok. destruct (fl y) as [a |] eqn:Hy.
    - intros H. split.
      + intros z Hz. eapply forallb_elements in H; eauto. now eapply web_eqb_eq.
      + intros Ht. eapply forallb_elements in H; eauto. now eapply web_eqb_eq.
    - intros H. eapply andb_prop in H. destruct H as [Hex Hw]. eapply web_eqb_eq in Hw. subst.
      split; eauto. intros z _. unfold spec.wcon. rewrite all_ex_isex; eauto.
  Qed.

  (** Every abstract argument / result / field, for the infinite set *)
  Definition all_args (p : aset -> bool) : bool := all_lists p (s_arg s) (s_adef s).
  Definition all_rets (p : aset -> bool) : bool := all_map p (s_ret s) (s_rdef s).
  Definition all_flds (p : aset -> bool) : bool := all_lists p (s_fld s) (s_fdef s).

  Lemma all_args_spec p : all_args p = true -> forall g i, p (Arg g i) = true.
  Proof. intros H g i. eapply (all_lists_spec p _ _ H). Qed.

  Lemma all_rets_spec p : all_rets p = true -> forall g, p (Ret g) = true.
  Proof. intros H g. eapply (all_map_spec p _ _ H). Qed.

  Lemma all_flds_spec p : all_flds p = true -> forall z i, p (Fld z i) = true.
  Proof. intros H z i. eapply (all_lists_spec p _ _ H). Qed.

  Definition app_b (f : var) (t : term.fun_tag) (w : web) (ys : list var) (Rs : aset) : bool :=
    let fun_ok g :=
      web_eqb (wfun g t) w &&
      forall_i (fun i y => sub_b (fl y) (Arg g i)) 0 ys &&
      sub_b (Ret g) Rs in
    match fl f with
    | AFin a =>
        forallb (fun l => match l with
                          | xO g => fun_ok g
                          | xH => web_eqb w (Exposed t) && ain_b ltop Rs
                          | _ => true
                          end) (PS.elements a)
    | AAll =>
        all_ex && web_eqb w (Exposed t) && ain_b ltop Rs &&
        forallb (fun y => all_args (sub_b (fl y))) ys &&
        all_rets (fun A => sub_b A Rs)
    end &&
    (negb (exposedb w) || forallb (fun y => esc_b (fl y)) ys).

  Lemma app_b_spec f t w ys Rs : app_b f t w ys Rs = true -> app_ok s f t w ys Rs.
  Proof.
    unfold app_b, app_ok. intros H. eapply andb_prop in H. destruct H as [H Hesc].
    split; [| split ].
    - intros g Hg. destruct (fl f) as [a |] eqn:Hf; simpl in Hg.
      + eapply forallb_elements in H; [| exact Hg ]. simpl in H.
        eapply andb_prop in H as [H Hr]. eapply andb_prop in H as [Hw Hargs].
        split; [ now eapply web_eqb_eq | split; [| now eapply sub_b_spec ] ].
        intros i y Hn. eapply sub_b_spec. eapply (forall_i_spec _ _ 0 Hargs); eauto.
      + repeat match goal with [ H : _ && _ = true |- _ ] => eapply andb_prop in H; destruct H end.
        eapply web_eqb_eq in H3. subst. split; [| split ].
        * unfold spec.wfun. rewrite all_ex_isex; eauto.
        * intros i y Hn. eapply sub_b_spec.
          eapply forallb_forall in H1; [| eapply nth_error_In; eassumption ].
          eapply all_args_spec; eauto.
        * eapply sub_b_spec. eapply (all_rets_spec (fun A => sub_b A Rs)); eauto.
    - intros Ht. destruct (fl f) as [a |] eqn:Hf; simpl in Ht.
      + eapply forallb_elements in H; [| exact Ht ]. simpl in H.
        eapply andb_prop in H as [Hw Hr]. split; [ now eapply web_eqb_eq | now eapply ain_b_spec ].
      + repeat match goal with [ H : _ && _ = true |- _ ] => eapply andb_prop in H; destruct H end.
        split; [ now eapply web_eqb_eq | now eapply ain_b_spec ].
    - intros Hw y Hy. rewrite Hw in Hesc. simpl in Hesc.
      eapply forallb_forall in Hesc; eauto. now eapply esc_b_spec.
  Qed.

  Definition labels_b : bool :=
    match s_ex s with
    | AAll => all_rets esc_b && all_args (ain_b ltop) && all_flds esc_b
    | AFin e =>
        forallb (fun l => match l with
                          | xO g => esc_b (Ret g) && ain_b ltop (s_adef s) &&
                                    forallb (ain_b ltop) (getd (s_arg s) [] g)
                          | xI z => esc_b (s_fdef s) && forallb esc_b (getd (s_fld s) [] z)
                          | xH => true
                          end) (PS.elements e)
    end.

  Lemma nth_forallb {A} (p : A -> bool) l d i : p d = true -> forallb p l = true -> p (nth i l d) = true.
  Proof.
    intros Hd Hl. destruct (nth_in_or_default i l d) as [Hin | Heq]; [| now rewrite Heq ].
    eapply forallb_forall in Hl; eauto.
  Qed.

  Lemma labels_b_spec : labels_b = true -> labels_ok s.
  Proof.
    unfold labels_b, labels_ok. destruct (s_ex s) as [e |] eqn:Hex; intros H.
    - split.
      + intros g Hg. simpl in Hg. eapply forallb_elements in H; [| exact Hg ]. simpl in H.
        repeat match goal with [ H : _ && _ = true |- _ ] => eapply andb_prop in H; destruct H end.
        split; [ now eapply esc_b_spec |].
        intros i. eapply ain_b_spec. unfold spec.Arg. eapply nth_forallb; eauto.
      + intros z Hz i. simpl in Hz. eapply forallb_elements in H; [| exact Hz ]. simpl in H.
        eapply andb_prop in H as [Hd Hl]. eapply esc_b_spec. unfold spec.Fld. eapply nth_forallb; eauto.
    - repeat match goal with [ H : _ && _ = true |- _ ] => eapply andb_prop in H; destruct H end.
      split.
      + intros g _. split; [ eapply esc_b_spec, (all_rets_spec esc_b); eauto |].
        intros i. eapply ain_b_spec, (all_args_spec (ain_b ltop)); eauto.
      + intros z _ i. eapply esc_b_spec, (all_flds_spec esc_b); eauto.
  Qed.

  (** The fields of the constructor labels flowing to [y], at position [n] *)
  Definition proj_b (y : var) (n : nat) (x : var) : bool :=
    match fl y with
    | AFin a =>
        forallb (fun l => match l with
                          | xI z => sub_b (Fld z n) (fl x)
                          | xH => ain_b ltop (fl x)
                          | _ => true
                          end) (PS.elements a)
    | AAll => all_flds (fun A => sub_b A (fl x)) && ain_b ltop (fl x)
    end.

  Lemma proj_b_spec y n x :
    proj_b y n x = true ->
    (forall z, ain (lcon z) (fl y) -> sub (Fld z n) (fl x)) /\
    (ain ltop (fl y) -> ain ltop (fl x)).
  Proof.
    unfold proj_b. destruct (fl y) as [a |] eqn:Hy; intros H.
    - split.
      + intros z Hz. eapply sub_b_spec. eapply forallb_elements in H; [| exact Hz ]; exact H.
      + intros Ht. eapply ain_b_spec. eapply forallb_elements in H; [| exact Ht ]; exact H.
    - eapply andb_prop in H as [Hf Ht]. split.
      + intros z _. eapply sub_b_spec. eapply (all_flds_spec (fun A => sub_b A (fl x))); eauto.
      + intros _. now eapply ain_b_spec.
  Qed.

  Fixpoint chk (R : aset) (e : term.exp) : bool :=
    match e with
    | term.Econstr x c ys e =>
        ain_b (lcon x) (fl x) && forall_i (fun i y => sub_b (fl y) (Fld x i)) 0 ys && chk R e
    | term.Ecase y cl =>
        use_b y (wuse y) &&
        (fix chk_br (cl : list (term.ctor_tag * term.exp)) :=
           match cl with
           | [] => true
           | (c, e) :: cl => chk R e && chk_br cl
           end) cl
    | term.Eproj x c n y e => use_b y (wuse y) && proj_b y (N.to_nat n) x && chk R e
    | term.Eletapp x f t ys e => app_b f t (wapp f t) ys (fl x) && chk R e
    | term.Efun B e => chk_fds B && chk R e
    | term.Eapp f t ys => app_b f t (wapp f t) ys R
    | term.Eprim_val x p e => chk R e
    | term.Eprim x p ys e => chk R e
    | term.Ehalt x => sub_b (fl x) R
    end
  with chk_fds (B : term.fundefs) : bool :=
    match B with
    | term.Fcons g t xs b B =>
        ain_b (lfun g) (fl g) && forall_i (fun i x => sub_b (Arg g i) (fl x)) 0 xs &&
        chk (Ret g) b && chk_fds B
    | term.Fnil => true
    end.

  Ltac andb_split :=
    repeat match goal with [ H : _ && _ = true |- _ ] => eapply andb_prop in H; destruct H end.

  Definition chk_P (e : term.exp) := forall R, chk R e = true -> ok w_con s R e (anno e).
  Definition chk_Q (B : term.fundefs) := chk_fds B = true -> ok_fundefs w_con s B (anno_fds B).

  Lemma chk_spec_e : forall e, chk_P e.
  Proof.
    eapply (term.exp_mut chk_P chk_Q); unfold chk_P, chk_Q; simpl; intros; andb_split.
    - constructor; eauto.
      + now eapply ain_b_spec.
      + intros i y Hn. eapply sub_b_spec. match goal with [ Hf : forall_i ?p 0 ?l = true, Hn : nth_error ?l ?i = Some ?y |- _ ] => exact (forall_i_spec p l 0 Hf i y Hn) end.
    - constructor. now eapply use_b_spec.
    - constructor; eauto.
    - edestruct proj_b_spec as [Hp1 Hp2]; eauto.
      constructor; eauto. now eapply use_b_spec.
    - constructor; eauto. now eapply app_b_spec.
    - constructor; eauto.
    - constructor. now eapply app_b_spec.
    - constructor; eauto.
    - constructor; eauto.
    - constructor. now eapply sub_b_spec.
    - constructor; eauto.
      + now eapply ain_b_spec.
      + intros i x Hn. eapply sub_b_spec. match goal with [ Hf : forall_i ?p 0 ?l = true, Hn : nth_error ?l ?i = Some ?y |- _ ] => exact (forall_i_spec p l 0 Hf i y Hn) end.
    - constructor.
  Qed.

  Lemma chk_spec_B : forall B, chk_Q B.
  Proof.
    eapply (term.fundefs_mut chk_P chk_Q); unfold chk_P, chk_Q; simpl; intros; andb_split.
    - constructor; eauto.
      + now eapply ain_b_spec.
      + intros i y Hn. eapply sub_b_spec. match goal with [ Hf : forall_i ?p 0 ?l = true, Hn : nth_error ?l ?i = Some ?y |- _ ] => exact (forall_i_spec p l 0 Hf i y Hn) end.
    - constructor. now eapply use_b_spec.
    - constructor; eauto.
    - edestruct proj_b_spec as [Hp1 Hp2]; eauto.
      constructor; eauto. now eapply use_b_spec.
    - constructor; eauto. now eapply app_b_spec.
    - constructor; eauto.
    - constructor. now eapply app_b_spec.
    - constructor; eauto.
    - constructor; eauto.
    - constructor. now eapply sub_b_spec.
    - constructor; eauto.
      + now eapply ain_b_spec.
      + intros i x Hn. eapply sub_b_spec. match goal with [ Hf : forall_i ?p 0 ?l = true, Hn : nth_error ?l ?i = Some ?y |- _ ] => exact (forall_i_spec p l 0 Hf i y Hn) end.
    - constructor.
  Qed.

  Lemma chk_spec :
    (forall e R, chk R e = true -> ok w_con s R e (anno e)) /\
    (forall B, chk_fds B = true -> ok_fundefs w_con s B (anno_fds B)).
  Proof. split; [ exact chk_spec_e | exact chk_spec_B ]. Qed.

  Definition check (R : aset) (e : term.exp) : bool :=
    labels_b && esc_b R && chk R e &&
    forallb (fun x => ain_b ltop (fl x)) (PS.elements (identifiers.exp_fv e)).

  Lemma check_spec R e : check R e = true -> ok_top w_con s R e (anno e).
  Proof.
    unfold check. intros H. andb_split.
    split; [ now eapply labels_b_spec |]. split; [ now eapply esc_b_spec |].
    split; [ now eapply chk_spec |].
    intros x Hx. eapply ain_b_spec.
    match goal with [ Hf : forallb _ (PS.elements (identifiers.exp_fv e)) = true |- _ ] =>
      exact (forallb_elements (fun x => ain_b ltop (fl x)) _ Hf x
                              (FromSet_sound _ _ _ (identifiers.exp_fv_correct e) Hx)) end.
  Qed.

End Check.

(** * The trivial solution: every value may flow everywhere and is exposed *)

Definition triv : sol :=
  mk_sol (M.empty _) AAll (M.empty _) AAll (M.empty _) AAll (M.empty _) AAll AAll (M.empty _).

Section Triv.

  Variable (w_con : web).

  Lemma triv_ok :
    (forall e, ok w_con triv AAll e (anno w_con triv e)) /\
    (forall B, ok_fundefs w_con triv B (anno_fds w_con triv B)).
  Proof.
    assert (Hfl : forall x, fl triv x = AAll) by reflexivity.
    assert (Hwf : forall g t, wfun triv g t = Exposed t) by reflexivity.
    assert (Hwc : forall z, wcon w_con triv z = w_con) by reflexivity.
    assert (Huse : forall y, use_ok w_con triv y w_con) by (intros; split; eauto).
    assert (Harg : forall g i, Arg triv g i = AAll)
      by (intros; unfold spec.Arg, getd; rewrite M.gempty; destruct i; reflexivity).
    assert (Hfld : forall z i, Fld triv z i = AAll)
      by (intros; unfold spec.Fld, getd; rewrite M.gempty; destruct i; reflexivity).
    assert (Happ : forall f t ys, app_ok triv f t (Exposed t) ys AAll).
    { intros. split; [| split ]; simpl; eauto.
      - intros g _. split; [ reflexivity | split; [ intros; intros l Hl; rewrite Harg; exact I | intros l Hl; exact I ] ].
      - intros _ y _ l _. right. exact I. }
    split; [ eapply (term.exp_mut (fun e => ok w_con triv AAll e (anno w_con triv e))
                                  (fun B => ok_fundefs w_con triv B (anno_fds w_con triv B)))
           | eapply (term.fundefs_mut (fun e => ok w_con triv AAll e (anno w_con triv e))
                                      (fun B => ok_fundefs w_con triv B (anno_fds w_con triv B))) ];
      simpl; intros;
      first [ now constructor
            | now constructor; eauto
            | constructor; [ exact I | intros i y _ l _; rewrite Hfld; exact I | eauto ]
            | constructor; [ exact (Huse _) | intros z _ l _; exact I | intros; exact I | eauto ]
            | constructor; [ exact (Huse _) ]
            | constructor; [ apply Happ | eauto ]
            | constructor; [ apply Happ ]
            | constructor; [ intros l _; exact I ]
            | constructor; [ exact I | intros i x _ l _; exact I | eauto | eauto ] ].
  Qed.

  Lemma triv_top e : ok_top w_con triv AAll e (anno w_con triv e).
  Proof.
    split; [| split; [| split ] ].
    - split; intros.
      + split; [ intros l _; right; exact I |].
        intros i. unfold spec.Arg, getd. rewrite M.gempty. destruct i; exact I.
      + intros l _. right. exact I.
    - intros l _. right. exact I.
    - eapply triv_ok.
    - intros; exact I.
  Qed.

End Triv.

(** * The solver *)

Record st : Type :=
  mk_st { st_v : M.t PS.t;           (* flows of variables *)
          st_a : M.t (list PS.t);    (* arguments of function labels *)
          st_f : M.t (list PS.t);    (* fields of constructor labels *)
          st_r : M.t PS.t;           (* results of function labels *)
          st_top : PS.t;             (* result of the program *)
          st_x : PS.t }.             (* exposed labels *)

Definition gv (m : M.t PS.t) (x : positive) : PS.t := getd m PS.empty x.
Definition gl (m : M.t (list PS.t)) (x : positive) : list PS.t := getd m [] x.

Fixpoint upd_nth (l : list PS.t) (i : nat) (A : PS.t) : list PS.t :=
  match l, i with
  | [], 0 => [A]
  | [], S i => PS.empty :: upd_nth [] i A
  | B :: l, 0 => PS.union B A :: l
  | B :: l, S i => B :: upd_nth l i A
  end.

Definition add_v (x : var) (A : PS.t) (s : st) : st :=
  mk_st (M.set x (PS.union (gv (st_v s) x) A) (st_v s)) (st_a s) (st_f s) (st_r s) (st_top s) (st_x s).
Definition add_a (g : var) (i : nat) (A : PS.t) (s : st) : st :=
  mk_st (st_v s) (M.set g (upd_nth (gl (st_a s) g) i A) (st_a s)) (st_f s) (st_r s) (st_top s) (st_x s).
Definition add_f (z : var) (i : nat) (A : PS.t) (s : st) : st :=
  mk_st (st_v s) (st_a s) (M.set z (upd_nth (gl (st_f s) z) i A) (st_f s)) (st_r s) (st_top s) (st_x s).
Definition add_r (g : var) (A : PS.t) (s : st) : st :=
  mk_st (st_v s) (st_a s) (st_f s) (M.set g (PS.union (gv (st_r s) g) A) (st_r s)) (st_top s) (st_x s).
Definition add_top (A : PS.t) (s : st) : st :=
  mk_st (st_v s) (st_a s) (st_f s) (st_r s) (PS.union (st_top s) A) (st_x s).
(** The labels of [A] escape *)
Definition escape (A : PS.t) (s : st) : st :=
  mk_st (st_v s) (st_a s) (st_f s) (st_r s) (st_top s) (PS.union (st_x s) (PS.remove ltop A)).
(** The arguments of an exposed function come from the context *)
Definition expose_args (g : var) (n : nat) (s : st) : st :=
  let l := gl (st_a s) g in
  let l := l ++ repeat PS.empty (n - length l) in
  mk_st (st_v s) (M.set g (map (PS.add ltop) l) (st_a s)) (st_f s) (st_r s) (st_top s) (st_x s).

(** Where results flow: a variable, the result of a function, or the
    result of the program *)
Inductive tgt := TVar (x : var) | TRet (g : var) | TTop.

Definition add_t (t : tgt) (A : PS.t) (s : st) : st :=
  match t with
  | TVar x => add_v x A s
  | TRet g => add_r g A s
  | TTop => add_top A s
  end.

Fixpoint fold_i {A B} (f : B -> nat -> A -> B) (i : nat) (l : list A) (b : B) : B :=
  match l with
  | [] => b
  | a :: l => fold_i f (S i) l (f b i a)
  end.

Definition kind_labels (fn : bool) (A : PS.t) : PS.t :=
  PS.filter (fun l => if fn then is_flab l else is_clab l) A.

(** A use site of [y]: if a value of the context or an exposed label of
    the right kind reaches it, all its labels of that kind are exposed. *)
Definition use_site (fn : bool) (y : var) (s : st) : st * bool :=
  let A := gv (st_v s) y in
  let K := kind_labels fn A in
  if PS.mem ltop A || negb (PS.is_empty (PS.inter K (st_x s))) then (escape K s, true) else (s, false).

Definition call (f : var) (ys : list var) (t : tgt) (s : st) : st :=
  let A := gv (st_v s) f in
  let '(s, ex) := use_site true f s in
  let s := PS.fold (fun l s =>
                      match l with
                      | xO g =>
                          let s := fold_i (fun s i y => add_a g i (gv (st_v s) y) s) 0 ys s in
                          add_t t (gv (st_r s) g) s
                      | _ => s
                      end) A s in
  let s := if PS.mem ltop A then add_t t (PS.singleton ltop) s else s in
  if ex then fold_left (fun s y => escape (gv (st_v s) y) s) ys s else s.

Fixpoint step (cur : tgt) (e : term.exp) (s : st) : st :=
  match e with
  | term.Econstr x c ys e =>
      let s := add_v x (PS.singleton (lcon x)) s in
      let s := fold_i (fun s i y => add_f x i (gv (st_v s) y) s) 0 ys s in
      let s := if PS.mem (lcon x) (st_x s) then fold_left (fun s A => escape A s) (gl (st_f s) x) s else s in
      step cur e s
  | term.Ecase y cl =>
      let s := fst (use_site false y s) in
      (fix step_br (cl : list (term.ctor_tag * term.exp)) (s : st) :=
         match cl with
         | [] => s
         | (_, e) :: cl => step_br cl (step cur e s)
         end) cl s
  | term.Eproj x c n y e =>
      let s := fst (use_site false y s) in
      let A := gv (st_v s) y in
      let s := PS.fold (fun l s =>
                          match l with
                          | xI z => add_v x (nth (N.to_nat n) (gl (st_f s) z) PS.empty) s
                          | xH => add_v x (PS.singleton ltop) s
                          | _ => s
                          end) A s in
      step cur e s
  | term.Eletapp x f t ys e => step cur e (call f ys (TVar x) s)
  | term.Efun B e => step cur e (step_fds B s)
  | term.Eapp f t ys => call f ys cur s
  | term.Eprim_val x p e => step cur e s
  | term.Eprim x p ys e => step cur e s
  | term.Ehalt x => add_t cur (gv (st_v s) x) s
  end
with step_fds (B : term.fundefs) (s : st) : st :=
  match B with
  | term.Fcons g t xs b B =>
      let s := add_v g (PS.singleton (lfun g)) s in
      let exg := PS.mem (lfun g) (st_x s) in
      let s := if exg then escape (gv (st_r s) g) (expose_args g (length xs) s) else s in
      let s := fold_i (fun s i x => add_v x (nth i (gl (st_a s) g) PS.empty) (add_a g i PS.empty s)) 0 xs s in
      step_fds B (step (TRet g) b s)
  | term.Fnil => s
  end.

(** ** Iteration with binary fuel

    [loop f stop p a] applies [f] at most [p] times, stopping with [Done] as
    soon as [stop a (f a)].  The fuel is a binary number, so a large bound
    costs nothing to compute. *)

Inductive res (A : Type) := Done (a : A) | More (a : A).
Arguments Done {A}.
Arguments More {A}.

Definition loop1 {A} (f : A -> A) (stop : A -> A -> bool) (a : A) : res A :=
  let a' := f a in if stop a a' then Done a' else More a'.

Definition bind_more {A} (r : res A) (k : A -> res A) : res A :=
  match r with Done a => Done a | More a => k a end.

Fixpoint loop {A} (f : A -> A) (stop : A -> A -> bool) (p : positive) (a : A) : res A :=
  match p with
  | xH => loop1 f stop a
  | xO p => bind_more (loop f stop p a) (loop f stop p)
  | xI p => bind_more (loop1 f stop a) (fun a => bind_more (loop f stop p a) (loop f stop p))
  end.

(** ** The universe of the program

    The variables of the program, its labels, and the largest arity.  The
    state only ever mentions these, so the part of the state within them
    bounds the number of rounds. *)

Definition add_list (l : list var) (acc : PS.t) : PS.t := fold_left (fun a x => PS.add x a) l acc.

Fixpoint vars_acc (e : term.exp) (acc : PS.t) : PS.t :=
  match e with
  | term.Econstr x _ ys e => vars_acc e (add_list (x :: ys) acc)
  | term.Ecase y cl =>
      (fix vars_br (cl : list (term.ctor_tag * term.exp)) (acc : PS.t) :=
         match cl with
         | [] => acc
         | (_, e) :: cl => vars_br cl (vars_acc e acc)
         end) cl (PS.add y acc)
  | term.Eproj x _ _ y e => vars_acc e (PS.add x (PS.add y acc))
  | term.Eletapp x f _ ys e => vars_acc e (add_list (x :: f :: ys) acc)
  | term.Efun B e => vars_acc e (vars_fds B acc)
  | term.Eapp f _ ys => add_list (f :: ys) acc
  | term.Eprim_val x _ e => vars_acc e (PS.add x acc)
  | term.Eprim x _ ys e => vars_acc e (add_list (x :: ys) acc)
  | term.Ehalt x => PS.add x acc
  end
with vars_fds (B : term.fundefs) (acc : PS.t) : PS.t :=
  match B with
  | term.Fcons g _ xs b B => vars_fds B (vars_acc b (add_list (g :: xs) acc))
  | term.Fnil => acc
  end.

Fixpoint arity (e : term.exp) : nat :=
  match e with
  | term.Econstr _ _ ys e | term.Eletapp _ _ _ ys e | term.Eprim _ _ ys e => Nat.max (length ys) (arity e)
  | term.Ecase _ cl =>
      (fix arity_br (cl : list (term.ctor_tag * term.exp)) :=
         match cl with
         | [] => 0
         | (_, e) :: cl => Nat.max (arity e) (arity_br cl)
         end) cl
  | term.Eproj _ _ _ _ e | term.Eprim_val _ _ e => arity e
  | term.Efun B e => Nat.max (arity_fds B) (arity e)
  | term.Eapp _ _ ys => length ys
  | term.Ehalt _ => 0
  end
with arity_fds (B : term.fundefs) : nat :=
  match B with
  | term.Fcons _ _ xs b B => Nat.max (length xs) (Nat.max (arity b) (arity_fds B))
  | term.Fnil => 0
  end.

Definition ulabels (vs : PS.t) : PS.t :=
  PS.fold (fun x U => PS.add (lfun x) (PS.add (lcon x) U)) vs (PS.singleton ltop).

(** ** The measure: the size of the state within the universe *)

Definition sum {A} (f : A -> nat) (l : list A) : nat := fold_right (fun a n => f a + n) 0 l.

Definition cnt (U : PS.t) (A : PS.t) : nat := PS.fold (fun l n => if PS.mem l U then S n else n) A 0.

Definition cnt_list (U : PS.t) (N : nat) (l : list PS.t) : nat :=
  Nat.min (length l) N + sum (fun i => cnt U (nth i l PS.empty)) (seq 0 N).

Definition umeasure (Ks : list var) (U : PS.t) (N : nat) (s : st) : nat :=
  sum (fun k => cnt U (gv (st_v s) k)) Ks + sum (fun k => cnt_list U N (gl (st_a s) k)) Ks +
  sum (fun k => cnt_list U N (gl (st_f s) k)) Ks + sum (fun k => cnt U (gv (st_r s) k)) Ks +
  cnt U (st_top s) + cnt U (st_x s).

(** A bound on [umeasure], computed in binary *)
Definition ubound (nk nu na : N) : N :=
  (nk * nu + nk * (na + na * nu) + nk * (na + na * nu) + nk * nu + nu + nu)%N.

Definition round (e : term.exp) (s : st) : st :=
  let s := step TTop e s in
  escape (st_top s) s.

Definition init (e : term.exp) : st :=
  let s := mk_st (M.empty _) (M.empty _) (M.empty _) (M.empty _) PS.empty PS.empty in
  fold_left (fun s x => add_v x (PS.singleton ltop) s) (PS.elements (identifiers.exp_fv e)) s.

(** ** Internal webs: the labels sharing a use site share a web *)

Fixpoint sites (e : term.exp) : list (bool * var) :=
  match e with
  | term.Econstr _ _ _ e | term.Eproj _ _ _ _ e | term.Eprim_val _ _ e | term.Eprim _ _ _ e => sites e
  | term.Ecase y cl =>
      (false, y) ::
      (fix sites_br (cl : list (term.ctor_tag * term.exp)) :=
         match cl with
         | [] => []
         | (_, e) :: cl => sites e ++ sites_br cl
         end) cl
  | term.Eletapp x f t ys e => (true, f) :: sites e
  | term.Efun B e => sites_fds B ++ sites e
  | term.Eapp f t ys => [(true, f)]
  | term.Ehalt _ => []
  end
with sites_fds (B : term.fundefs) : list (bool * var) :=
  match B with
  | term.Fcons _ _ _ b B => sites b ++ sites_fds B
  | term.Fnil => []
  end.

Definition find_w (iw : M.t positive) (l : lab) : positive := getd iw l l.

Definition merge_site (s : st) (iw : M.t positive) (site : bool * var) : M.t positive :=
  let '(fn, y) := site in
  let K := PS.elements (PS.diff (kind_labels fn (gv (st_v s) y)) (st_x s)) in
  match K with
  | [] => iw
  | l :: _ =>
      let m := fold_left (fun m l => Pos.min m (find_w iw l)) K (find_w iw l) in
      fold_left (fun iw l => M.set l m iw) K iw
  end.

Definition iw_eqb (ls : list lab) (iw1 iw2 : M.t positive) : bool :=
  forallb (fun l => Pos.eqb (find_w iw1 l) (find_w iw2 l)) ls.

(** Each pass only lowers webs, so the sum of the webs of the labels bounds
    the number of passes. *)
Definition merge_fuel (ls : list lab) : positive :=
  N.succ_pos (fold_left (fun n l => (n + Npos l)%N) ls 0%N).

Definition merge_loop (s : st) (ss : list (bool * var)) (ls : list lab) : res (M.t positive) :=
  loop (fun iw => fold_left (merge_site s) ss iw) (iw_eqb ls) (merge_fuel ls) (M.empty _).

Definition all_labels (s : st) : list lab :=
  PS.elements (M.fold1 (fun acc A => PS.union acc A) (st_v s) PS.empty).

Definition webs_of (e : term.exp) (s : st) : M.t positive :=
  let ls := all_labels s in
  let iw := match merge_loop s (sites e) ls with Done iw | More iw => iw end in
  fold_left (fun m l => M.set l (find_w iw l) m) ls (M.empty _).

Definition sol_of (e : term.exp) (s : st) : sol * aset :=
  (mk_sol (M.map1 AFin (st_v s)) (AFin PS.empty)
          (M.map1 (map AFin) (st_a s)) AAll
          (M.map1 (map AFin) (st_f s)) (AFin PS.empty)
          (M.map1 AFin (st_r s)) (AFin PS.empty)
          (AFin (st_x s)) (webs_of e s),
   AFin (st_top s)).

(** The rounds of the solver, with fuel one more than the bound on the
    measure *)
Definition solve_loop (e : term.exp) : res st :=
  let vs := vars_acc e PS.empty in
  let Ks := PS.elements vs in
  let U := ulabels vs in
  let N := arity e in
  let fuel := N.succ_pos (ubound (N.of_nat (length Ks)) (N.of_nat (PS.cardinal U)) (N.of_nat N)) in
  loop (round e) (fun s s' => Nat.eqb (umeasure Ks U N s') (umeasure Ks U N s)) fuel (init e).

Definition solve (e : term.exp) : option (sol * aset) :=
  match solve_loop e with
  | Done s => Some (sol_of e s)
  | More _ => None
  end.

(** * The analysis *)

Section Analysis.

  Variable (w_con : web).
  Hypothesis (Hw_con : exposedb w_con = true).

  Definition analyze (e : term.exp) : sol * aset :=
    match solve e with
    | Some (s, R) => if check w_con s R e then (s, R) else (triv, AAll)
    | None => (triv, AAll)
    end.

  Definition annotate (e : term.exp) : exp :=
    let '(s, _) := analyze e in anno w_con s e.

  Lemma analyze_ok e : let '(s, R) := analyze e in ok_top w_con s R e (anno w_con s e).
  Proof.
    unfold analyze. destruct (solve e) as [[s R] |]; [| eapply triv_top ].
    destruct (check w_con s R e) eqn:Hc; [ eapply check_spec; eauto | eapply triv_top ].
  Qed.

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  (** The analysis inhabits the annotation relation. *)
  Theorem annotate_correct cenv e :
    E_anno_top cenv w_con (P_eq (fuel := fuel) (trace := trace)) P_eq e (annotate e).
  Proof.
    unfold annotate. pose proof (analyze_ok e) as Hok.
    destruct (analyze e) as [s R]. eapply ok_top_E_anno; eauto.
  Qed.

End Analysis.
