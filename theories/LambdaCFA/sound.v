(* Soundness of the 0-CFA constraints: a program satisfying [ok_top] is
   related to its annotation by the annotation relation of
   [LambdaWeb/anno.v].

   The proof uses a cross-language logical relation indexed by abstract
   values: [V k A v1 v2] relates a λANF value to its annotated λweb
   counterpart when
   - [ltop] is in [A] and the values are related by the interface relation
     [V_a] (a value of the unknown context), or
   - [v1] is a constructor allocated at a site [z] with [lcon z] in [A],
     annotated with the web of [z], with fields related at the abstract
     fields of [z], or
   - [v1] is a closure of [f] with [lfun f] in [A], annotated with the web of
     [f], whose body is related when called with arguments related at the
     abstract arguments of [f], returning results related at the abstract
     result of [f].

   Two lemmas connect it with the interface: [V_import] (a value of the
   context is related at any set containing [ltop]) and [V_export] (a value
   related at an escaping set is related by [V_a]).  The analysis does not
   change the steps of the program, so the source and the annotated program
   use the same fuel ([P_eq]). *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics algebra set_util.
From CertiRocq.LambdaANF Require term term_util identifiers.
From CertiRocq.LambdaANF Require eval rel_comp.
From CertiRocq.LambdaWeb Require Import syntax semantics erase anno.
From CertiRocq.LambdaCFA Require Import spec.

Import ListNotations.

Open Scope alg_scope.

(** Lists related pointwise, with the position *)
Fixpoint Forall2i {A B} (P : nat -> A -> B -> Prop) (i : nat) (l1 : list A) (l2 : list B) : Prop :=
  match l1, l2 with
  | [], [] => True
  | a :: l1, b :: l2 => P i a b /\ Forall2i P (S i) l1 l2
  | _, _ => False
  end.

Lemma Forall2i_mono {A B} (P Q : nat -> A -> B -> Prop) i l1 l2 :
  (forall j a b, P j a b -> Q j a b) -> Forall2i P i l1 l2 -> Forall2i Q i l1 l2.
Proof.
  intros H. revert i l2; induction l1; intros i [| b l2]; simpl; try easy;
    intros [H1 H2]; eauto.
Qed.

Lemma Forall2i_length {A B} (P : nat -> A -> B -> Prop) i l1 l2 :
  Forall2i P i l1 l2 -> length l1 = length l2.
Proof. revert i l2; induction l1; intros i [| b l2]; simpl; try easy; intros [_ H]; f_equal; eauto. Qed.

Lemma Forall2i_Forall2 {A B} (P : A -> B -> Prop) i l1 l2 :
  Forall2i (fun _ => P) i l1 l2 -> Forall2 P l1 l2.
Proof. revert i l2; induction l1; intros i [| b l2]; simpl; try easy; intros [H1 H2]; eauto. Qed.

Lemma Forall2_Forall2i {A B} (P : A -> B -> Prop) i l1 l2 :
  Forall2 P l1 l2 -> Forall2i (fun _ => P) i l1 l2.
Proof. intros H; revert i; induction H; intros i; simpl; eauto. Qed.

Lemma Forall2i_nthN {A B} (P : nat -> A -> B -> Prop) i l1 l2 n a :
  Forall2i P i l1 l2 -> nthN l1 n = Some a ->
  exists b, nthN l2 n = Some b /\ P (i + N.to_nat n) a b.
Proof.
  revert i l2 n; induction l1 as [| a' l1 IH]; intros i [| b l2] n Hall Hn; simpl in *; try easy.
  destruct Hall as [H1 H2]. destruct n as [| p].
  - inv Hn. eexists; split; [ reflexivity |]. replace (i + N.to_nat 0) with i by lia. exact H1.
  - edestruct IH as (b' & Hb' & HP); eauto.
    eexists; split; [ eassumption |].
    replace (i + N.to_nat (N.pos p)) with (S i + N.to_nat (N.pos p - 1)) by lia. exact HP.
Qed.

Lemma Forall2i_aux_eq {A B} (Vi : aset -> A -> B -> Prop) (F : var -> nat -> aset) z i
      (vs1 : list A) (vs2 : list B) :
  (fix aux (z : var) (i : nat) (vs1 : list A) (vs2 : list B) {struct vs1} : Prop :=
     match vs1, vs2 with
     | [], [] => True
     | v1 :: vs1, v2 :: vs2 => Vi (F z i) v1 v2 /\ aux z (S i) vs1 vs2
     | _, _ => False
     end) z i vs1 vs2 <-> Forall2i (fun i => Vi (F z i)) i vs1 vs2.
Proof.
  revert i vs2; induction vs1; intros i vs2; destruct vs2; simpl; try easy.
  rewrite IHvs1. reflexivity.
Qed.

Section Sound.

  Variable (cenv : term.ctor_env).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Local Notation PostT_a := (@PostT_a fuel trace).

  Variable (w_con : web).
  Hypothesis (Hw_con : exposedb w_con = true).
  Variable (s : sol).

  Local Notation fl := (fl s).
  Local Notation Arg := (Arg s).
  Local Notation Fld := (Fld s).
  Local Notation Ret := (Ret s).
  Local Notation wfun := (wfun s).
  Local Notation wcon := (wcon w_con s).
  Local Notation esc := (esc s).

  (** The analysis keeps the steps of the program. *)
  Definition P_eq : PostT_a :=
    fun p1 p2 => let '(_, _, c1, _) := p1 in let '(_, _, c2, _) := p2 in c1 = c2.

  Local Notation V_a := (V_a cenv w_con P_eq).

  (** ** The relation *)

  Definition E' (V : nat -> aset -> aval -> val -> Prop) (ex : bool) (R : aset) (k : nat)
             (p1 : term.exp * aenv) (p2 : exp * env) : Prop :=
    let '(e1, rho1) := p1 in
    let '(e2, rho2) := p2 in
    forall r1 cin cout,
      to_nat cin <= k ->
      abstep_fuel cenv rho1 e1 cin r1 cout ->
      exists r2 cout',
        bstep_fuel cenv ex rho2 e2 cin r2 cout' /\
        R_a' (fun j => V j R) (k - to_nat cin) r1 r2.

  Definition V_fun (V' : nat -> aset -> aval -> val -> Prop) (k : nat) (v1 : aval) (v2 : val) : Prop :=
    match v1, v2 with
    | term.Vfun rho1 B1 f1, Vfun rho2 B2 f2 =>
        exists t xs1 e1 xs2 e2,
          term.find_def f1 B1 = Some (t, xs1, e1) /\
          find_def f2 B2 = Some (wfun f1 t, xs2, e2) /\
          length xs1 = length xs2 /\
          forall vs1 vs2 j rho1' rho2',
            j < k ->
            set_lists xs1 vs1 (term.def_funs B1 B1 rho1 rho1) = Some rho1' ->
            set_lists xs2 vs2 (def_funs B2 B2 rho2 rho2) = Some rho2' ->
            Forall2i (fun i => V' j (Arg f1 i)) 0 vs1 vs2 ->
            E' V' (exposedb (wfun f1 t)) (Ret f1) j (e1, rho1') (e2, rho2')
    | _, _ => False
    end.

  Fixpoint V (k : nat) (A : aset) (v1 : aval) (v2 : val) {struct k} : Prop :=
    let V' : nat -> aset -> aval -> val -> Prop :=
      match k with
      | 0 => fun _ _ _ _ => False
      | S k0 => fun j => V (k0 - (k0 - j))
      end in
    let fix Vi (A : aset) (v1 : aval) (v2 : val) {struct v1} : Prop :=
      let fix aux (z : var) (i : nat) (vs1 : list aval) (vs2 : list val) {struct vs1} : Prop :=
        match vs1, vs2 with
        | [], [] => True
        | v1 :: vs1, v2 :: vs2 => Vi (Fld z i) v1 v2 /\ aux z (S i) vs1 vs2
        | _, _ => False
        end in
      wf_val v2 /\
      ((ain ltop A /\ V_a k v1 v2) \/
       match v1, v2 with
       | term.Vconstr c1 vs1, Vconstr w c2 vs2 =>
           c1 = c2 /\ exists z, ain (lcon z) A /\ w = wcon z /\ aux z 0 vs1 vs2
       | term.Vfun _ _ f1, Vfun _ _ _ => ain (lfun f1) A /\ V_fun V' k v1 v2
       | term.Vprim p1, Vprim p2 => p1 = p2
       | term.Vint z1, Vint z2 => z1 = z2
       | _, _ => False
       end)
    in Vi A v1 v2.

  Definition V_ (k : nat) (A : aset) (v1 : aval) (v2 : val) : Prop :=
    wf_val v2 /\
    ((ain ltop A /\ V_a k v1 v2) \/
     match v1, v2 with
     | term.Vconstr c1 vs1, Vconstr w c2 vs2 =>
         c1 = c2 /\ exists z, ain (lcon z) A /\ w = wcon z /\ Forall2i (fun i => V k (Fld z i)) 0 vs1 vs2
     | term.Vfun _ _ f1, Vfun _ _ _ => ain (lfun f1) A /\ V_fun V k v1 v2
     | term.Vprim p1, Vprim p2 => p1 = p2
     | term.Vint z1, Vint z2 => z1 = z2
     | _, _ => False
     end).

  Lemma E'_ext V1 V2 ex R k p1 p2 :
    (forall j, j <= k -> forall A v1 v2, V1 j A v1 v2 <-> V2 j A v1 v2) ->
    E' V1 ex R k p1 p2 -> E' V2 ex R k p1 p2.
  Proof.
    destruct p1 as [e1 rho1], p2 as [e2 rho2]. simpl.
    intros Hext HE r1 cin cout Hleq Hstep.
    edestruct HE as (r2 & cout' & Hstep' & HR); eauto.
    do 2 eexists; split; [ eassumption |].
    destruct r1, r2; simpl in *; eauto. eapply Hext; eauto. lia.
  Qed.

  Lemma V_fun_ext V1 V2 k v1 v2 :
    (forall j, j < k -> forall A v1 v2, V1 j A v1 v2 <-> V2 j A v1 v2) ->
    V_fun V1 k v1 v2 -> V_fun V2 k v1 v2.
  Proof.
    destruct v1, v2; unfold V_fun; try easy.
    intros Hext (ft & xs1 & e1 & xs2 & e2 & Hf1 & Hf2 & Hlen & Hbody).
    do 5 eexists. split; [ eassumption | split; [ eassumption | split; [ eassumption |] ] ].
    intros vs1 vs2 j rho1' rho2' Hlt Hs1 Hs2 Hall.
    eapply E'_ext; [| eapply Hbody; eauto ].
    - intros. eapply Hext. lia.
    - eapply Forall2i_mono; [| eassumption ]. intros. eapply Hext; eauto.
  Qed.

  Lemma V_fun_mono V k j v1 v2 : V_fun V k v1 v2 -> j <= k -> V_fun V j v1 v2.
  Proof.
    destruct v1, v2; unfold V_fun; try easy.
    intros (ft & xs1 & e1 & xs2 & e2 & Hf1 & Hf2 & Hlen & Hbody) Hleq.
    do 5 eexists. split; [ eassumption | split; [ eassumption | split; [ eassumption |] ] ].
    intros. eapply Hbody; eauto. lia.
  Qed.

  Lemma V_eq k A v1 v2 : V k A v1 v2 <-> V_ k A v1 v2.
  Proof.
    revert A v2. induction v1 using aval_ind_Forall; intros A v2;
      unfold V_; destruct k as [| k0]; cbn -[V_fun V_a]; try reflexivity.
    - destruct v2; try reflexivity.
      setoid_rewrite Forall2i_aux_eq. reflexivity.
    - destruct v2; try reflexivity.
      setoid_rewrite Forall2i_aux_eq. reflexivity.
    - split; intros (H1 & H2); (split; [ eassumption |]);
        (destruct H2 as [H2 | H2]; [ now left | right ]); destruct v2; try easy;
        (split; [ apply H2 |]); eapply V_fun_ext; try apply H2; intros; lia.
    - split; intros (H1 & H2); (split; [ eassumption |]);
        (destruct H2 as [H2 | H2]; [ now left | right ]); destruct v2; try easy;
        (split; [ apply H2 |]); eapply V_fun_ext; try apply H2;
        intros j Hj; cbv beta; replace (k0 - (k0 - j)) with j by lia; reflexivity.
  Qed.

  Global Opaque V.

  Lemma V_wf k A v1 v2 : V k A v1 v2 -> wf_val v2.
  Proof. rewrite V_eq. intros H; apply H. Qed.

  Lemma V_mono k : forall j A v1 v2, V k A v1 v2 -> j <= k -> V j A v1 v2.
  Proof.
    intros j A v1. revert j A. induction v1 using aval_ind_Forall; intros j A v2 Hv Hleq;
      rewrite V_eq in *; unfold V_ in *; destruct Hv as [Hwf Hv]; (split; [ exact Hwf |]);
      (destruct Hv as [[Htop Ha] | Hv]; [ left; split; [ exact Htop | eapply V_a_mono; eauto ] | right ]).
    - destruct v2; try contradiction. destruct Hv as (Hc & z & Hz & Hw & Hall).
      split; [ exact Hc |]. exists z. split; [ exact Hz | split; [ exact Hw |] ].
      clear -H Hall Hleq. revert Hall. generalize 0.
      revert l; induction H; intros [| v2 vs2] i Hall; simpl in *; try easy;
      destruct Hall as [H1 H2]; split; eauto.
    - destruct v2; try contradiction. destruct Hv as [Hfn Hv].
      split; [ exact Hfn | eapply V_fun_mono; eauto ].
    - exact Hv.
    - exact Hv.
  Qed.

  Lemma V_sub k : forall A B v1 v2, V k A v1 v2 -> sub A B -> V k B v1 v2.
  Proof.
    intros A B v1 v2 Hv Hs. rewrite V_eq in *. unfold V_ in *.
    destruct Hv as [Hwf Hv]. split; [ exact Hwf |].
    destruct Hv as [[Htop Ha] | Hv]; [ left; split; eauto | right ].
    destruct v1, v2; try contradiction; eauto.
    - destruct Hv as (Hc & z & Hz & Hw & Hall). split; eauto.
    - destruct Hv as [Hfn Hv]. split; eauto.
  Qed.

  (** ** Import and export *)

  Lemma V_import k A v1 v2 : ain ltop A -> V_a k v1 v2 -> V k A v1 v2.
  Proof.
    intros Htop Hv. rewrite V_eq. split; [ eapply V_a_wf; eauto |]. left; eauto.
  Qed.

  Lemma esc_lcon A z : esc A -> ain (lcon z) A -> isex s (lcon z) = true.
  Proof. intros He Hz. destruct (He _ Hz) as [Heq | Hin]; [ discriminate | now eapply isex_ain ]. Qed.

  Lemma esc_lfun A f : esc A -> ain (lfun f) A -> isex s (lfun f) = true.
  Proof. intros He Hg. destruct (He _ Hg) as [Heq | Hin]; [ discriminate | now eapply isex_ain ]. Qed.

  Lemma V_export (Hl : labels_ok s) k : forall A v1 v2, esc A -> V k A v1 v2 -> V_a k v1 v2.
  Proof.
    induction k as [k IHk] using lt_wf_rec.
    intros A v1. revert A. induction v1 using aval_ind_Forall; intros A v2 He Hv;
      rewrite V_eq in Hv; unfold V_ in Hv; destruct Hv as [Hwf [[Htop Ha] | Hv]]; try exact Ha.
    - destruct v2; try contradiction. destruct Hv as (Hc & z & Hz & Hw & Hall). subst.
      assert (Hex := esc_lcon _ _ He Hz).
      assert (Hwz : wcon z = w_con) by (unfold spec.wcon; rewrite Hex; reflexivity).
      assert (Hvs : Forall2 (V_a k) vs l).
      { clear -H Hall Hl Hex. revert Hall. generalize 0.
        revert l; induction H; intros [| v2 vs2] i Hall; simpl in *; try easy;
        destruct Hall as [H1 H2]; constructor; eauto;
        eapply H; [| eassumption ]; eapply Hl; now eapply isex_ain. }
      rewrite V_a_eq. split; [ exact Hwf |]. split.
      + rewrite exposed_val_Vconstr. split; [ rewrite Hwz; exact Hw_con |].
        clear -Hvs. induction Hvs; constructor; eauto. eapply V_a_exposed; eauto.
      + rewrite Hwz. split; [ reflexivity | split; [ reflexivity | exact Hvs ] ].
    - destruct v2 as [? ? ? | rho2 B2 f2 | ? | ?]; try contradiction. destruct Hv as [Hfn Hfun].
      assert (Hex := esc_lfun _ _ He Hfn).
      assert (Hwt : forall t, wfun f t = Exposed t) by (intros; unfold spec.wfun; rewrite Hex; reflexivity).
      destruct Hfun as (t & xs1 & e1 & xs2 & e2 & Hf1 & Hf2 & Hlen & Hbody).
      rewrite Hwt in Hf2.
      rewrite V_a_eq. split; [ exact Hwf |]. split.
      + rewrite exposed_val_Vfun. eauto.
      + simpl. intros vs1 vs2 j t' xs1' e1' rho1' Hlen' Hf1' Hset1.
        rewrite Hf1 in Hf1'. inv Hf1'.
        edestruct (set_lists_length3 (def_funs B2 B2 rho2 rho2) xs2 vs2) as [rho2' Hset2].
        { symmetry in Hset1. eapply set_lists_length_eq in Hset1.
          transitivity (length xs1'); [ symmetry; exact Hlen | transitivity (length vs1); [ exact Hset1 | exact Hlen' ] ]. }
        do 3 eexists. split; [ eassumption | split; [ symmetry; eassumption |] ].
        intros Hlt Hall r1 cin cout Hleq Hstep.
        edestruct (Hbody vs1 vs2 j) as (r2 & cout' & Hstep2 & HR); eauto.
        * eapply Forall2_Forall2i in Hall. eapply Forall2i_mono; [| exact Hall ].
          intros i a b Hab. eapply V_import; [ eapply Hl; now eapply isex_ain | exact Hab ].
        * rewrite Hwt in Hstep2. simpl in Hstep2.
          do 3 eexists. split; [ exact Hstep2 | split; [ reflexivity |] ].
          destruct r1, r2; simpl in *; eauto.
          eapply (IHk (j - to_nat cin)); [ lia | | exact HR ].
          eapply Hl. now eapply isex_ain.
    - destruct v2; try contradiction. subst.
      rewrite V_a_eq. split; [ exact Hwf | split; [ exact I | reflexivity ] ].
    - destruct v2; try contradiction. subst.
      rewrite V_a_eq. split; [ exact Hwf | split; [ exact I | reflexivity ] ].
  Qed.

  Lemma R_mono R k j r1 r2 :
    R_a' (fun j => V j R) k r1 r2 -> j <= k -> R_a' (fun j => V j R) j r1 r2.
  Proof. destruct r1, r2; simpl; eauto. intros. eapply V_mono; eauto. Qed.

  Lemma R_sub R R' k r1 r2 :
    R_a' (fun j => V j R) k r1 r2 -> sub R R' -> R_a' (fun j => V j R') k r1 r2.
  Proof. destruct r1, r2; simpl; eauto. intros. eapply V_sub; eauto. Qed.

  Lemma R_exposed (Hl : labels_ok s) ex R k r1 r2 :
    (ex = true -> esc R) -> R_a' (fun j => V j R) k r1 r2 -> ex = true -> exposed_res r2.
  Proof.
    intros Hex HR Heq. destruct r1, r2; simpl in *; try easy.
    eapply V_a_exposed. eapply V_export; eauto.
  Qed.

  Lemma Forall2i_exposed (Hl : labels_ok s) (F : nat -> aset) k n vs1 vs2 :
    (forall i, esc (F i)) -> Forall2i (fun i => V k (F i)) n vs1 vs2 -> Forall exposed_val vs2.
  Proof.
    intros Hesc. revert n vs2; induction vs1; intros n [| v2 vs2] Hall; simpl in *; try easy;
      constructor; [| eapply IHvs1; apply Hall ].
    eapply V_a_exposed. eapply V_export; eauto. apply Hall.
  Qed.

  Lemma Forall2i_wf (F : nat -> aset) k n vs1 vs2 :
    Forall2i (fun i => V k (F i)) n vs1 vs2 -> Forall wf_val vs2.
  Proof.
    revert n vs2; induction vs1; intros n [| v2 vs2] Hall; simpl in *; try easy;
      constructor; [ eapply V_wf; apply Hall | eapply IHvs1; apply Hall ].
  Qed.

  (** ** Environments *)

  Definition var_rel k (rho1 : aenv) (rho2 : env) (x : var) : Prop :=
    forall v1, M.get x rho1 = Some v1 -> exists v2, M.get x rho2 = Some v2 /\ V k (fl x) v1 v2.

  Definition G k (Sv : Ensemble var) (rho1 : aenv) (rho2 : env) : Prop :=
    wf_env rho2 /\ forall x, Sv x -> var_rel k rho1 rho2 x.

  Lemma G_mono k j Sv rho1 rho2 : G k Sv rho1 rho2 -> j <= k -> G j Sv rho1 rho2.
  Proof.
    intros [Hwf HG] Hleq. split; eauto. intros x Hx v1 Hget.
    edestruct HG as (v2 & Hget2 & Hv); eauto. eexists; split; eauto. eapply V_mono; eauto.
  Qed.

  Lemma G_antimon k Sv Sv' rho1 rho2 : G k Sv rho1 rho2 -> Sv' \subset Sv -> G k Sv' rho1 rho2.
  Proof. intros [Hwf HG] Hs. split; eauto. intros x Hx. eapply HG. eapply Hs. exact Hx. Qed.

  Lemma G_set k Sv rho1 rho2 x v1 v2 :
    G k (Sv \\ [set x]) rho1 rho2 -> V k (fl x) v1 v2 ->
    G k Sv (M.set x v1 rho1) (M.set x v2 rho2).
  Proof.
    intros [Hwf HG] Hv. split; [ eapply wf_env_set; eauto; eapply V_wf; eauto |].
    intros y Hy v1' Hget. destruct (peq y x); subst.
    - rewrite M.gss in Hget. inv Hget. rewrite M.gss. eauto.
    - rewrite M.gso in Hget by auto. rewrite M.gso by auto.
      eapply HG; eauto. constructor; eauto. intros Hc; inv Hc; eauto.
  Qed.

  Lemma G_get_list k Sv rho1 rho2 ys vs1 (Q : nat -> aval -> val -> Prop) n :
    G k Sv rho1 rho2 -> FromList ys \subset Sv ->
    (forall i y v1 v2, nth_error ys i = Some y -> V k (fl y) v1 v2 -> Q (n + i) v1 v2) ->
    get_list ys rho1 = Some vs1 ->
    exists vs2, get_list ys rho2 = Some vs2 /\ Forall2i Q n vs1 vs2.
  Proof.
    intros HG. revert n vs1. induction ys as [| y ys IH]; intros n vs1 Hsub HQ Hget; simpl in *.
    - inv Hget. eexists; split; [ reflexivity | exact I ].
    - destruct (M.get y rho1) as [v1 |] eqn:Hy; try congruence.
      destruct (get_list ys rho1) as [vs1' |] eqn:Hys; try congruence. inv Hget.
      edestruct (proj2 HG y) as (v2 & Hy2 & Hv); [ eapply Hsub; now left | eassumption |].
      edestruct (IH (S n) vs1') as (vs2 & Hys2 & Hall); [ | | reflexivity |].
      + intros z Hz. eapply Hsub. now right.
      + intros i y' v1' v2' Hn Hv'. replace (S n + i) with (n + S i) by lia. eapply HQ; eauto.
      + rewrite Hy2, Hys2. eexists; split; [ reflexivity |]. simpl. split; eauto.
        replace n with (n + 0) by lia. eapply HQ; eauto. reflexivity.
  Qed.

  Lemma G_set_lists k Sv rho1 rho2 xs vs1 vs2 rho1' rho2' (F : nat -> aset) n :
    G k (Sv \\ FromList xs) rho1 rho2 ->
    Forall2i (fun i => V k (F i)) n vs1 vs2 ->
    (forall i x, nth_error xs i = Some x -> sub (F (n + i)) (fl x)) ->
    set_lists xs vs1 rho1 = Some rho1' -> set_lists xs vs2 rho2 = Some rho2' ->
    G k Sv rho1' rho2'.
  Proof.
    revert Sv n vs1 vs2 rho1' rho2'.
    induction xs as [| x xs IH]; intros Sv n [| v1 vs1] [| v2 vs2] rho1' rho2' HG Hall Hsub Hs1 Hs2;
      simpl in *; try congruence; try contradiction.
    - inv Hs1; inv Hs2. eapply G_antimon; [ eassumption |]. intros z Hz. constructor; eauto.
    - destruct (set_lists xs vs1 rho1) as [r1 |] eqn:Hr1; try congruence.
      destruct (set_lists xs vs2 rho2) as [r2 |] eqn:Hr2; try congruence. inv Hs1; inv Hs2.
      destruct Hall as [Hv Hall]. eapply G_set.
      + eapply (IH _ (S n)); eauto.
        * eapply G_antimon; eauto. intros z [[Hz Hnx] Hnxs]. constructor; eauto.
          intros Hc; inv Hc; eauto.
        * intros i y Hn. replace (S n + i) with (n + S i) by lia. eapply Hsub. exact Hn.
      + eapply V_sub; eauto. replace n with (n + 0) by lia. eapply Hsub. reflexivity.
  Qed.

  Lemma G_def_funs k Sv rho1 rho2 rho1c rho2c B1 B2 :
    G k (Sv \\ name_in_fundefs B2) rho1 rho2 ->
    ok_fundefs w_con s B1 B2 ->
    wf_env rho2c ->
    (forall g, name_in_fundefs B2 g -> V k (fl g) (term.Vfun rho1c B1 g) (Vfun rho2c B2 g)) ->
    G k Sv (term.def_funs B1 B1 rho1c rho1) (def_funs B2 B2 rho2c rho2).
  Proof.
    intros [Hwf HG] Hok Hwfc Hclo. split; [ eapply wf_env_def_funs; eauto |].
    intros x Hx v1 Hget. destruct (name_in_fundefs_dec B2 x) as [Hin | Hnin].
    - rewrite identifiers.def_funs_eq in Hget by (eapply (ok_fundefs_names _ _ _ _ Hok); exact Hin).
      inv Hget. rewrite def_funs_eq by exact Hin. eauto.
    - rewrite identifiers.def_funs_neq in Hget
        by (intros Hc; eapply Hnin; eapply (ok_fundefs_names _ _ _ _ Hok); exact Hc).
      rewrite def_funs_neq by exact Hnin. eapply HG; eauto. constructor; eauto.
  Qed.

  Lemma to_nat_one_w1 (e : exp) : to_nat (one_w e : fuel) = 1.
  Proof. unfold one_w, algebra.one. eapply to_nat_one. Qed.

  Lemma to_nat_one_a1 (e : term.exp) : to_nat (algebra.one e : fuel) = 1.
  Proof. unfold algebra.one. eapply to_nat_one. Qed.

  Ltac fuel_arith :=
    repeat match goal with
           | [ H : context [ to_nat (_ <+> _) ] |- _ ] => rewrite to_nat_add in H
           | [ |- context [ to_nat (_ <+> _) ] ] => rewrite to_nat_add
           | [ H : context [ to_nat (one_w _) ] |- _ ] => rewrite to_nat_one_w1 in H
           | [ |- context [ to_nat (one_w _) ] ] => rewrite to_nat_one_w1
           | [ H : context [ to_nat (algebra.one _) ] |- _ ] => rewrite to_nat_one_a1 in H
           | [ |- context [ to_nat (algebra.one _) ] ] => rewrite to_nat_one_a1
           end; lia.

  (** ** Closures *)

  Lemma V_clo (Hl : labels_ok s) k rho1 rho2 B1 B2 :
    (forall m R e1 e2 ex rho1 rho2,
        m < k -> ok w_con s R e1 e2 -> (ex = true -> esc R) ->
        G m (occurs_free e2) rho1 rho2 -> E' V ex R m (e1, rho1) (e2, rho2)) ->
    ok_fundefs w_con s B1 B2 ->
    G k (occurs_free_fundefs B2) rho1 rho2 ->
    forall g, name_in_fundefs B2 g -> V k (fl g) (term.Vfun rho1 B1 g) (Vfun rho2 B2 g).
  Proof.
    induction k as [k IHk] using lt_wf_rec. intros Hfund Hok HG g Hg.
    edestruct name_in_fundefs_find_def as (w & xs & b2 & Hf2); eauto.
    edestruct ok_fundefs_find_def_r as (t & b1 & Hf1 & Hw); eauto. subst.
    edestruct ok_fundefs_find_def as (b2' & Hf2' & Hokb & Hgin & Hargs); eauto.
    rewrite Hf2 in Hf2'. inv Hf2'.
    rewrite V_eq. split; [ constructor; apply HG |]. right. split; [ exact Hgin |].
    do 5 eexists. split; [ eassumption | split; [ eassumption | split; [ reflexivity |] ] ].
    intros vs1 vs2 j rho1' rho2' Hlt Hs1 Hs2 Hall.
    eapply Hfund; [ eassumption | eassumption | |].
    - rewrite exposedb_wfun. intros Hex. eapply Hl. now eapply isex_ain.
    - eapply G_antimon; [| eapply occurs_free_in_fun; eassumption ].
      eapply (G_set_lists _ _ _ _ _ _ _ _ _ _ 0); eauto.
      eapply G_def_funs; eauto.
      + eapply G_antimon; [ eapply G_mono; [ exact HG | lia ] |]. eapply fun_body_scope_subset.
      + apply HG.
      + intros h Hh. eapply IHk; eauto.
        * intros. eapply Hfund; eauto. lia.
        * eapply G_mono; eauto. lia.
  Qed.


  (** A call: the λANF callee runs its body; the λweb callee too, at the
      web of the call site, with a related result. *)
  Lemma call_rel (Hl : labels_ok s) m Sv f t w ys Rs rho1 rho2 rhoc B h vs1 xs1 b1 rhoc' cin1 r1 cout1 :
    app_ok s f t w ys Rs ->
    G m Sv rho1 rho2 -> Sv f -> FromList ys \subset Sv ->
    M.get f rho1 = Some (term.Vfun rhoc B h) ->
    get_list ys rho1 = Some vs1 ->
    term.find_def h B = Some (t, xs1, b1) ->
    set_lists xs1 vs1 (term.def_funs B B rhoc rhoc) = Some rhoc' ->
    abstep_fuel cenv rhoc' b1 cin1 r1 cout1 ->
    to_nat cin1 < m ->
    exists rhoc2 B2 h2 vs2 xs2 b2 rhoc2' r2 cout2,
      M.get f rho2 = Some (Vfun rhoc2 B2 h2) /\
      get_list ys rho2 = Some vs2 /\
      find_def h2 B2 = Some (w, xs2, b2) /\
      set_lists xs2 vs2 (def_funs B2 B2 rhoc2 rhoc2) = Some rhoc2' /\
      (exposedb w = true -> Forall exposed_val vs2) /\
      bstep_fuel cenv (exposedb w) rhoc2' b2 cin1 r2 cout2 /\
      R_a' (fun j => V j Rs) (m - 1 - to_nat cin1) r1 r2.
  Proof.
    intros (Hlab & Htop & Hexw) HG Hfin Hys Hgetf Hgetl Hfd Hset Hbody Hlt.
    edestruct (proj2 HG f Hfin) as (v2f & Hgetf2 & Hvf); [ eassumption |].
    rewrite V_eq in Hvf. destruct Hvf as [Hwf [[Htp Ha] | Hv]].
    - (* a function of the context *)
      destruct (Htop Htp) as [Hw Htop']. subst w.
      assert (Hexa : forall i y v1 v2, nth_error ys i = Some y -> V m (fl y) v1 v2 -> V_a m v1 v2).
      { intros i y v1 v2 Hn Hv. eapply V_export; eauto. eapply Hexw; [ reflexivity |].
        eapply nth_error_In; eassumption. }
      edestruct (G_get_list m _ _ _ ys vs1 (fun _ => V_a m) 0 HG Hys) as (vs2 & Hgetl2 & Hvs);
        [ intros; eapply Hexa; eauto | eassumption |].
      eapply Forall2i_Forall2 in Hvs.
      rewrite V_a_eq in Ha. destruct Ha as (_ & _ & Ha).
      destruct v2f as [? ? ? | rhoc2 B2 h2 | ? | ?]; try contradiction.
      edestruct (Ha vs1 vs2 (m - 1) t xs1 b1 rhoc') as (xs2 & b2 & rhoc2' & Hfd2 & Hset2 & Hb);
        [ eapply Forall2_length; eauto | eassumption | symmetry; eassumption |].
      edestruct Hb as (r2 & cin' & cout2 & Hstep2 & Heq & HR);
        [ lia | | | eassumption | ].
      + eapply Forall2_monotonic; [| eassumption ]. intros. eapply V_a_mono; eauto. lia.
      + lia.
      + simpl in Heq. subst cin'.
        do 9 eexists. split; [ eassumption | split; [ eassumption | split; [ eassumption | split ] ] ].
        * symmetry; eassumption.
        * split; [| split; [ exact Hstep2 |] ].
          -- intros _. clear -Hvs. induction Hvs; constructor; eauto. eapply V_a_exposed; eauto.
          -- destruct r1, r2; simpl in *; eauto. eapply V_import; eauto.
    - (* a closure of the program *)
      destruct v2f as [? ? ? | rhoc2 B2 h2 | ? | ?]; try contradiction.
      destruct Hv as [Hh Hfun].
      destruct Hfun as (t' & xs1' & b1' & xs2 & b2 & Hfd1 & Hfd2 & Hlen & Hfbody).
      rewrite Hfd in Hfd1. inv Hfd1.
      destruct (Hlab _ Hh) as (Hw & Hargs & Hret). rewrite Hw in Hfd2.
      edestruct (G_get_list m _ _ _ ys vs1
                   (fun i v1 v2 => V m (Arg h i) v1 v2 /\ (exposedb w = true -> exposed_val v2)) 0 HG Hys)
        as (vs2 & Hgetl2 & Hvs); [ | eassumption |].
      { intros i y v1 v2 Hn Hv. split.
        - eapply V_sub; eauto.
        - intros Hew. eapply V_a_exposed. eapply V_export; eauto. eapply Hexw; eauto.
          eapply nth_error_In; eassumption. }
      assert (Hlen2 : length xs2 = length vs2).
      { erewrite <- (Forall2i_length _ _ _ _ Hvs). eapply set_lists_length_eq in Hset.
        transitivity (length xs1'); [ symmetry; exact Hlen | exact Hset ]. }
      edestruct (set_lists_length3 (def_funs B2 B2 rhoc2 rhoc2) xs2 vs2 Hlen2) as [rhoc2' Hset2].
      edestruct (Hfbody vs1 vs2 (m - 1) rhoc' rhoc2') as (r2 & cout2 & Hstep2 & HR);
        [ lia | eassumption | eassumption | | | eassumption |].
      + eapply Forall2i_mono; [| exact Hvs ]. intros i a b [Hab _]. eapply V_mono; eauto. lia.
      + lia.
      + rewrite Hw in Hstep2.
        do 9 eexists. split; [ eassumption | split; [ eassumption | split; [ eassumption | split ] ] ].
        * eassumption.
        * split; [| split; [ exact Hstep2 | eapply R_sub; eauto ] ].
          intros Hew. eapply Forall2i_mono with (Q := fun _ _ b => exposed_val b) in Hvs;
            [| intros i a b [_ Hb]; eauto ].
          clear -Hvs. revert Hvs. generalize 0. revert vs2.
          induction vs1; intros [| v2 vs2] i Hall; simpl in Hall; try contradiction.
          -- constructor.
          -- constructor; [ apply Hall | eapply IHvs1; apply Hall ].
  Qed.

  (** ** The fundamental property *)

  Lemma ok_case_use R y w cl1 cl2 :
    ok w_con s R (term.Ecase y cl1) (Ecase y w cl2) -> use_ok w_con s y w.
  Proof.
    revert cl1. induction cl2 as [| [c e2] cl2 IH]; intros cl1 Hok; inv Hok; eauto.
  Qed.

  Lemma V_scrut k y w c vs1 v2 :
    use_ok w_con s y w -> V k (fl y) (term.Vconstr c vs1) v2 ->
    exists vs2, v2 = Vconstr w c vs2 /\
      ((ain ltop (fl y) /\ Forall2 (V_a k) vs1 vs2) \/
       (exists z, ain (lcon z) (fl y) /\ Forall2i (fun i => V k (Fld z i)) 0 vs1 vs2)).
  Proof.
    intros [Hcon Htop] Hv. rewrite V_eq in Hv. destruct Hv as [Hwf [[Htp Ha] | Hv]].
    - rewrite V_a_eq in Ha. destruct Ha as (_ & _ & Ha). destruct v2; try contradiction.
      destruct Ha as (Hw & Hc & Hall). subst. rewrite (Htop Htp). eauto.
    - destruct v2; try contradiction. destruct Hv as (Hc & z & Hz & Hw & Hall). subst.
      rewrite (Hcon _ Hz). eauto 10.
  Qed.

  Lemma Res_inv (r : res) k R v1 :
    R_a' (fun j => V j R) k (aRes v1) r -> exists v2, r = Res v2 /\ V k R v1 v2.
  Proof. destruct r; simpl; try easy; eauto. Qed.

  Lemma fundamental (Hl : labels_ok s) k :
    forall R e1 e2 ex rho1 rho2,
      ok w_con s R e1 e2 -> (ex = true -> esc R) ->
      G k (occurs_free e2) rho1 rho2 ->
      E' V ex R k (e1, rho1) (e2, rho2).
  Proof.
    induction k as [k IHk] using lt_wf_rec.
    intros R e1 e2 ex rho1 rho2 Hok. revert ex rho1 rho2.
    cut (forall m ex rho1 rho2, m <= k -> (ex = true -> esc R) ->
                                G m (occurs_free e2) rho1 rho2 -> E' V ex R m (e1, rho1) (e2, rho2)).
    { intros H ex rho1 rho2. eapply H; eauto. }
    induction Hok; intros m ex rho1 rho2 Hmk Hex HG r1 cin cout Hleq Hstep;
      (inv Hstep; [ exists OOT, <0>; split; [ constructor; eassumption | exact I ] |]);
      match goal with [ H : CertiRocq.LambdaANF.eval.bstep _ _ _ _ _ _ |- _ ] => inv H end.
    - (* Econstr *)
      edestruct (G_get_list m _ _ _ ys vs (fun i => V m (Fld x i)) 0 HG) as (vs2 & Hgl & Hvs);
        [ normalize_occurs_free; sets | | eassumption |].
      { intros i y v1 v2 Hn Hv. eapply V_sub; eauto. }
      assert (Hexp : exposedb (wcon x) = true -> Forall exposed_val vs2).
      { rewrite exposedb_wcon by exact Hw_con. intros Hx.
        eapply Forall2i_exposed; [ eassumption | | exact Hvs ].
        intros i. eapply Hl. now eapply isex_ain. }
      assert (Hv : V m (fl x) (term.Vconstr c vs) (Vconstr (wcon x) c vs2)).
      { rewrite V_eq. split.
        - constructor; [ exact Hexp | eapply Forall2i_wf; eauto ].
        - right. split; [ reflexivity |]. eexists; eauto. }
      edestruct IHHok as (r2 & cout2 & Hstep2 & HR);
        [ exact Hmk | exact Hex | | | eassumption | ].
      + eapply G_set; eauto. eapply G_antimon; eauto. normalize_occurs_free. sets.
      + fuel_arith.
      + do 2 eexists. split.
        * econstructor 2; [ econstructor; eauto | eapply R_exposed; eauto ].
        * eapply R_mono; eauto. fuel_arith.
    - (* Eproj *)
      edestruct (proj2 HG y) as (v2y & Hgety & Hvy); [ fv_mem | eassumption |].
      edestruct V_scrut as (vs2 & Heq & Hcase); eauto. subst.
      assert (Hfld : exists v2, nthN vs2 n = Some v2 /\ V m (fl x) v v2).
      { destruct Hcase as [[Htp Hall] | (z & Hz & Hall)].
        - eapply Forall2_Forall2i with (i := 0) in Hall.
          edestruct (Forall2i_nthN _ _ _ _ _ _ Hall H13) as (v2 & Hn2 & Hv2).
          eexists; split; eauto. eapply V_import; eauto.
        - edestruct (Forall2i_nthN _ _ _ _ _ _ Hall H13) as (v2 & Hn2 & Hv2).
          eexists; split; eauto. eapply V_sub; eauto. }
      destruct Hfld as (v2 & Hn2 & Hv2).
      edestruct IHHok as (r2 & cout2 & Hstep2 & HR);
        [ exact Hmk | exact Hex | | | eassumption | ].
      + eapply G_set; eauto. eapply G_antimon; eauto. normalize_occurs_free. sets.
      + fuel_arith.
      + do 2 eexists. split.
        * econstructor 2; [ econstructor; eauto | eapply R_exposed; eauto ].
        * eapply R_mono; eauto. fuel_arith.
    - (* Ecase [] *)
      match goal with [ H : term_util.find_tag_nth [] _ _ _ |- _ ] => inv H end.
    - (* Ecase (_ :: _) *)
      edestruct (proj2 HG y) as (v2y & Hgety & Hvy); [ fv_mem | eassumption |].
      edestruct V_scrut as (vs2 & Heq & _); [ eapply ok_case_use; eassumption | eassumption |]. subst.
      assert (Hcc : term_util.caseConsistent cenv (erase_branches ((c, e2) :: cl2)) t).
      { eapply term_util.caseConsistent_same_ctor_tags; [| eassumption ].
        eapply ok_one_case. econstructor; eassumption. }
      match goal with [ Hft : term_util.find_tag_nth ((_, _) :: _) _ _ _ |- _ ] => inv Hft end.
      + edestruct IHHok1 as (r2 & cout2 & Hstep2 & HR);
          [ exact Hmk | exact Hex | | | eassumption | ].
        * eapply G_antimon; eauto. normalize_occurs_free. sets.
        * fuel_arith.
        * do 2 eexists. split.
          -- econstructor 2; [ econstructor; eauto; constructor | eapply R_exposed; eauto ].
          -- eapply R_mono; eauto. fuel_arith.
      + assert (Hcc1 : term_util.caseConsistent cenv cl1 t).
        { match goal with [ Hc : term_util.caseConsistent _ ((_, _) :: _) _ |- _ ] => inv Hc; eassumption end. }
        edestruct IHHok2 as (r2 & cout2 & Hstep2 & HR);
          [ exact Hmk | exact Hex | | | econstructor 2; econstructor; eassumption | ].
        * eapply G_antimon; eauto. normalize_occurs_free. sets.
        * eassumption.
        * inv Hstep2.
          -- exists OOT, <0>. split; [ econstructor 1; eassumption | exact HR ].
          -- match goal with [ Hb : bstep _ _ _ (Ecase _ _ _) _ _ _ |- _ ] => inv Hb end.
             repeat subst_exp.
             assert (cin = cin0) by (eapply plus_inv; exact H). subst.
             do 2 eexists. split; [| exact HR ].
             econstructor 2; [| eassumption ].
             econstructor; eauto. constructor; eauto.
    - (* Eletapp, the body returns *)
      match goal with [ Happ : app_ok _ _ _ _ _ _ |- _ ] => rename Happ into Happ' end.
      edestruct (call_rel Hl m (occurs_free (Eletapp x f w ys e2)) f t w ys (spec.fl s x)) as
        (rhoc2 & B2 & h2 & vs2 & xs2 & b2 & rhoc2' & r2 & cout2' & Hgf & Hgl & Hfd & Hset & Hexp & Hb & HR);
        [ exact Happ' | exact HG | fv_mem | normalize_occurs_free; sets
        | eassumption | eassumption | eassumption | eassumption | eassumption | fuel_arith |].
      edestruct Res_inv as (v2 & Heq & Hv2); eauto. subst r2.
      edestruct (IHHok (m - 1 - to_nat cin1)) as (r2 & cout3 & Hstep2 & HR2);
        [ fuel_arith | exact Hex | | | eassumption | ].
      + eapply G_set; eauto. eapply G_antimon; [ eapply G_mono; [ exact HG | lia ] |].
        normalize_occurs_free. sets.
      + fuel_arith.
      + do 2 eexists. split.
        * econstructor 2; [ econstructor; eauto | eapply R_exposed; eauto ].
        * eapply R_mono; eauto. fuel_arith.
    - (* Eletapp, the body runs out of fuel *)
      match goal with [ Happ : app_ok _ _ _ _ _ _ |- _ ] => rename Happ into Happ' end.
      edestruct (call_rel Hl m (occurs_free (Eletapp x f w ys e2)) f t w ys (spec.fl s x)) as
        (rhoc2 & B2 & h2 & vs2 & xs2 & b2 & rhoc2' & r2 & cout2' & Hgf & Hgl & Hfd & Hset & Hexp & Hb & HR);
        [ exact Happ' | exact HG | fv_mem | normalize_occurs_free; sets
        | eassumption | eassumption | eassumption | eassumption | eassumption | fuel_arith |].
      destruct r2; try contradiction.
      do 2 eexists. split.
      + econstructor 2; [ eapply BStept_letapp_oot; eauto | intros; exact I ].
      + exact I.
    - (* Efun *)
      edestruct IHHok as (r2 & cout2 & Hstep2 & HR);
        [ exact Hmk | exact Hex | | | eassumption | ].
      + eapply G_def_funs; eauto.
        * eapply G_antimon; eauto. normalize_occurs_free. sets.
        * apply HG.
        * eapply V_clo; eauto.
          -- intros. eapply IHk; eauto. lia.
          -- eapply G_antimon; eauto. eapply occurs_free_fundefs_Efun_Included.
      + fuel_arith.
      + do 2 eexists. split.
        * econstructor 2; [ econstructor; eauto | eapply R_exposed; eauto ].
        * eapply R_mono; eauto. fuel_arith.
    - (* Eapp *)
      match goal with [ Happ : app_ok _ _ _ _ _ _ |- _ ] => rename Happ into Happ' end.
      edestruct (call_rel Hl m (occurs_free (Eapp f w ys)) f t w ys R) as
        (rhoc2 & B2 & h2 & vs2 & xs2 & b2 & rhoc2' & r2 & cout2' & Hgf & Hgl & Hfd & Hset & Hexp & Hb & HR);
        [ exact Happ' | exact HG | fv_mem | normalize_occurs_free; sets
        | eassumption | eassumption | eassumption | eassumption | eassumption | fuel_arith |].
      do 2 eexists. split.
      + econstructor 2; [ econstructor; eauto | eapply R_exposed; eauto ].
      + eapply R_mono; eauto. fuel_arith.
    - (* Ehalt *)
      edestruct (proj2 HG x) as (v2 & Hget2 & Hv); [ fv_mem | eassumption |].
      assert (HR : R_a' (fun j => V j R) (m - to_nat (<0> <+> algebra.one (term.Ehalt x))) (aRes v) (Res v2)).
      { simpl. eapply V_sub; [| eassumption ]. eapply V_mono; eauto. lia. }
      do 2 eexists. split.
      + econstructor 2; [ econstructor; eauto | eapply R_exposed; eauto ].
      + exact HR.
  Qed.

  (** ** The annotation relation *)

  Theorem ok_top_E_anno R e1 e2 :
    ok_top w_con s R e1 e2 -> E_anno_top cenv w_con P_eq P_eq e1 e2.
  Proof.
    intros (Hl & Hesc & Hok & Hfv).
    assert (Hfv12 := proj1 (ok_occurs_free w_con s) _ _ _ Hok).
    split; [ intros z Hz; eapply Hfv12; exact Hz |].
    intros k rho1 rho2 [Hwf HGa] Hbind. unfold E_a, E_a'. intros r1 cin cout Hleq Hstep.
    edestruct (fundamental Hl k R e1 e2 true rho1 rho2) as (r2 & cout' & Hstep2 & HR);
      [ exact Hok | intros _; exact Hesc | | eassumption | eassumption |].
    - split; [ exact Hwf |]. intros x Hx v1 Hget.
      assert (Hx1 : identifiers.occurs_free e1 x) by (eapply Hfv12; exact Hx).
      edestruct HGa as (v2 & Hget2 & Hv); eauto. eexists; split; eauto. eapply V_import; eauto.
    - exists r2, cin, cout'. split; [ exact Hstep2 | split; [ reflexivity |] ].
      destruct r1, r2; simpl in *; eauto. eapply V_export; eauto.
  Qed.

  Lemma P_eq_properties : Post_properties_a cenv P_eq P_eq.
  Proof.
    constructor.
    - intros B1 e1 rho1 B2 e2 rho2 c1 c2 cout1 cout2 H. simpl in *. subst. reflexivity.
    - intros x f1 f2 t ys1 ys2 e1 rho1 e2 rho2 xs e_b1 v1 e_b2 v2 rhoc1 rhoc2 B h vs rhoc1'
             c1 c1' c2 c2' cout1 cout2 cout1' cout2' _ _ _ _ _ H1 H2.
      simpl in *. subst. reflexivity.
    - intros x f1 f2 t ys1 ys2 e1 rho1 e2 rho2 xs e_b1 e_b2 rhoc1 rhoc2 B h vs rhoc1'
             c1 c2 cout1 cout2 _ _ _ _ H1.
      simpl in *. subst. reflexivity.
    - intros e1 rho1 e2 rho2 c _. simpl. reflexivity.
    - intros c1 c2 H. exact H.
  Qed.

  Lemma P_eq_upper_bound : post_a_upper_bound P_eq.
  Proof.
    intros e1 rho1 e2 rho2. exists (fun c => c).
    intros cin1 cin2 cout1 cout2 H. simpl in H. subst.
    exists <0>. rewrite plus_zero. reflexivity.
  Qed.

End Sound.
