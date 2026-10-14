(* An implementation of defunctionalization, and the proof that it inhabits
   the relation of defunc.v.

   The input is a lambda-lifted program [Efun Btop e0].
   - The analysis selects the internal webs whose functions are all wrappers
     [f xs = code (xs ++ zs)] of code functions of [Btop], assigns a fresh
     constructor tag to every wrapper, and a fresh inductive type to every
     selected web, whose constructors are the tags of its wrappers (its
     lambda set).  It returns the lambda sets [L], the table [T] from tags to
     code functions, and the extended constructor environment.
   - The transformation replaces the closures of the selected webs by records
     and their calls by a dispatch.  The continuation of a bound call is
     duplicated if it is small, and put in a join point otherwise.  The
     variables receiving the fields and the join points are fresh.
   - The checker [dfn_ok] checks the side conditions of the relation; it is
     proven sound.  If it fails, the program is left unchanged. *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics set_util.
From CertiRocq.LambdaANF Require term.
From CertiRocq.LambdaWeb Require Import syntax semantics exposed post select indep comp dpe dpe_impl cp cp_impl defunc.

Import ListNotations.

(** * Boolean helpers *)

Definition memb (z : var) (l : list var) : bool := existsb (Pos.eqb z) l.

Lemma memb_spec z l : memb z l = true <-> List.In z l.
Proof.
  unfold memb. rewrite existsb_exists. split.
  - intros (y & Hy & Heq). apply Pos.eqb_eq in Heq. subst. eassumption.
  - intros H. exists z. split; [ eassumption | apply Pos.eqb_refl ].
Qed.

Lemma memb_false z l : memb z l = false -> ~ List.In z l.
Proof. intros H Hc. eapply memb_spec in Hc. congruence. Qed.

Lemma bnames_name_in B x : List.In x (bnames B) -> name_in_fundefs B x.
Proof.
  induction B; simpl; intros H; [| contradiction ].
  destruct H as [-> | H]; [ left; constructor | right; eauto ].
Qed.

Lemma bnames_fnames B : bnames B = fnames B.
Proof. induction B; simpl; congruence. Qed.

Fixpoint prefixb (xs ys : list var) : bool :=
  match xs, ys with
  | [], _ => true
  | x :: xs, y :: ys => Pos.eqb x y && prefixb xs ys
  | _ :: _, [] => false
  end.

Lemma prefixb_spec xs ys : prefixb xs ys = true -> ys = xs ++ skipn (length xs) ys.
Proof.
  revert ys; induction xs as [| x xs IH]; intros ys H.
  - reflexivity.
  - destruct ys as [| y ys]; [ discriminate |]. simpl in H.
    apply andb_true_iff in H. destruct H as [H1 H2]. apply Pos.eqb_eq in H1. subst.
    simpl. f_equal. eapply IH; eauto.
Qed.

Lemma forallb_disjoint (zs : list var) (S : Ensemble var) (p : var -> bool) :
  (forall z, p z = false -> ~ S z) ->
  forallb (fun z => negb (p z)) zs = true -> Disjoint _ (FromList zs) S.
Proof.
  intros Hp Hf. constructor. intros z Hz. destruct Hz as [z Hz1 Hz2].
  eapply forallb_forall in Hf; [| exact Hz1 ]. apply negb_true_iff in Hf. eapply Hp; eassumption.
Qed.

(** * The transformation *)

(** The fields of a wrapper *)
Definition wrapper_fields (xs : list var) (e : exp) : option (var * web * list var) :=
  match e with
  | Eapp code wc args => if prefixb xs args then Some (code, wc, skipn (length xs) args) else None
  | _ => None
  end.

Lemma wrapper_fields_spec xs e code wc zs :
  wrapper_fields xs e = Some (code, wc, zs) -> e = Eapp code wc (xs ++ zs).
Proof.
  destruct e; simpl; try congruence. destruct (prefixb xs l) eqn:Hp; try congruence.
  intros H. inv H. f_equal. eapply prefixb_spec; eassumption.
Qed.

Section Transform.

  Variables (L : WM.t (list ctor_tag)) (T : M.t (var * web * nat)) (Btop : fundefs).
  Variable (tagof : M.t ctor_tag).   (* the tags of the wrappers *)
  Variable (m : var).                (* the variables above [m] are fresh *)
  Variable (thr : nat).              (* largest continuation that is duplicated *)
  Variable (jw : positive).          (* the index of the (fresh, internal) web of join points *)

  Definition jweb : web := Internal jw.

  Definition in_code (z : var) : bool := memb z (bnames Btop).

  Lemma in_code_false z : in_code z = false -> ~ Code Btop z.
  Proof. unfold in_code. intros H Hc. eapply memb_false; [ eassumption | eapply name_in_bnames; eassumption ]. Qed.

  Lemma in_code_true z : in_code z = true -> Code Btop z.
  Proof. unfold in_code. intros H. eapply bnames_name_in. eapply memb_spec. eassumption. Qed.

  Definition fresh_vars (n : nat) : list var := map (fun i => (m + Pos.of_nat (S (S i)))%positive) (seq 0 n).
  Definition jvar : var := (m + 1)%positive.

  Lemma fresh_vars_length n : length (fresh_vars n) = n.
  Proof. unfold fresh_vars. rewrite length_map, length_seq. reflexivity. Qed.

  Definition mk_alt (c : ctor_tag) : alt :=
    match T ! c with
    | Some (code, wc, n) => (c, code, wc, fresh_vars n)
    | None => (c, 1%positive, Internal 1%positive, [])
    end.

  Definition alts_of (w : web) : list alt :=
    match WM.get w L with Some lams => map mk_alt lams | None => [] end.

  Lemma alts_of_tags w lams : WM.get w L = Some lams -> map alt_tag (alts_of w) = lams.
  Proof.
    unfold alts_of. intros H. rewrite H. rewrite map_map.
    erewrite map_ext; [ apply map_id |]. intros c. unfold mk_alt.
    destruct (T ! c) as [[[? ?] ?] |]; reflexivity.
  Qed.

  Definition sel_w (w : web) : bool := keeps (sel_L L) w.

  (** The records of the wrappers of a bundle *)
  Fixpoint recs_of (B : fundefs) : list rec :=
    match B with
    | Fcons f w xs e B =>
        if sel_w w then recs_of B
        else match wrapper_fields xs e, tagof ! f with
             | Some (_, _, zs), Some c => (f, w, c, zs) :: recs_of B
             | _, _ => recs_of B
             end
    | Fnil => []
    end.

  Fixpoint dfn (e : exp) : exp :=
    match e with
    | Econstr x w t ys k => Econstr x w t ys (dfn k)
    | Eproj x w t n y k => Eproj x w t n y (dfn k)
    | Ecase x w cl =>
        Ecase x w ((fix go (cl : list (ctor_tag * exp)) :=
                      match cl with
                      | [] => []
                      | (c, e) :: cl => (c, dfn e) :: go cl
                      end) cl)
    | Eletapp x f w ys k =>
        if sel_w w then Eletapp x f w ys (dfn k)
        else if Nat.leb (esize k) thr then
               dispatch f w (alts_of w) (fun code wc zs => Eletapp x code wc (ys ++ zs) (dfn k))
             else
               Efun (Fcons jvar jweb [x] (dfn k) Fnil)
                    (dispatch f w (alts_of w) (fun code wc zs => Eletapp x code wc (ys ++ zs) (Eapp jvar jweb [x])))
    | Eapp f w ys =>
        if sel_w w then Eapp f w ys
        else dispatch f w (alts_of w) (fun code wc zs => Eapp code wc (ys ++ zs))
    | Efun B k => fun_recs (dfn_fd (recs_of B) B) (recs_of B) (dfn k)
    | Eprim_val x p k => Eprim_val x p k
    | Eprim x p ys k => Eprim x p ys k
    | Ehalt x => Ehalt x
    end
  with dfn_fd (rs0 : list rec) (B : fundefs) : fundefs :=
    match B with
    | Fcons f w xs e B =>
        if sel_w w then Fcons f w xs (bind_recs rs0 (dfn e)) (dfn_fd rs0 B) else dfn_fd rs0 B
    | Fnil => Fnil
    end.

  (** ** The checker *)

  Definition alts_okb (w : web) (avoid : var -> bool) : bool :=
    match WM.get w L with
    | Some lams =>
        forallb (fun c => match T ! c with
                          | Some (code, wc, n) =>
                              nodupb (fresh_vars n) &&
                              forallb (fun z => negb (avoid z || in_code z)) (fresh_vars n)
                          | None => false
                          end) lams
    | None => false
    end.

  (** The wrapper conditions of [TB_sel] *)
  Definition wrapper_okb (f : var) (w : web) (xs : list var) (e : exp) : bool :=
    match wrapper_fields xs e, tagof ! f, WM.get w L with
    | Some (code, wc, zs), Some c, Some lams =>
        memb c lams &&
        match T ! c with
        | Some (code', wc', n) => Pos.eqb code code' && web_eqb wc wc' && Nat.eqb n (length zs)
        | None => false
        end &&
        in_code code && negb (exposedb wc) && negb (sel_L L wc) &&
        nodupb xs && forallb (fun z => negb (memb z zs)) xs && negb (memb code xs)
    | _, _, _ => false
    end.

  Fixpoint dfn_ok (e : exp) : bool :=
    match e with
    | Econstr x w t ys k => negb (in_code x) && dfn_ok k
    | Eproj x w t n y k => negb (in_code x) && dfn_ok k
    | Ecase x w cl =>
        (fix go (cl : list (ctor_tag * exp)) :=
           match cl with
           | [] => true
           | (c, e) :: cl => dfn_ok e && go cl
           end) cl
    | Eletapp x f w ys k =>
        negb (in_code x) && dfn_ok k &&
        (sel_w w ||
         (if Nat.leb (esize k) thr then
            alts_okb w (fun z => Pos.eqb z f || memb z ys || is_free k z)
          else
            negb (in_code jvar) && negb (Pos.eqb jvar x) && negb (Pos.eqb jvar f) &&
            negb (memb jvar ys) && negb (is_free k jvar) &&
            alts_okb w (fun z => Pos.eqb z f || memb z ys || Pos.eqb z jvar)))
    | Eapp f w ys => sel_w w || alts_okb w (fun z => Pos.eqb z f || memb z ys)
    | Efun B k =>
        let rs := recs_of B in
        nodupb (bnames B) && forallb (fun f => negb (in_code f)) (bnames B) &&
        forallb (fun z => negb (memb z (rec_names rs))) (rec_fields rs) &&
        dfn_ok_fd (recs_of B) B && dfn_ok k
    | Eprim_val _ _ _ | Eprim _ _ _ _ | Ehalt _ => true
    end
  with dfn_ok_fd (rs0 : list rec) (B : fundefs) : bool :=
    match B with
    | Fcons f w xs e B =>
        (if sel_w w then
           forallb (fun z => negb (in_code z || memb z (rec_fields rs0) || memb z (rec_names rs0))) xs &&
           dfn_ok e
         else wrapper_okb f w xs e) &&
        dfn_ok_fd rs0 B
    | Fnil => true
    end.

  (** ** Soundness of the checker *)

  Lemma alts_okb_spec w (avoid : var -> bool) (S : Ensemble var) :
    (forall z, avoid z = false -> ~ S z) ->
    alts_okb w avoid = true -> alts_ok L T Btop w (alts_of w) S.
  Proof.
    unfold alts_okb. intros HS H. destruct (WM.get w L) as [lams |] eqn:HL; [| discriminate ].
    split; [ rewrite (alts_of_tags w lams HL); exact HL |].
    unfold alts_of. rewrite HL. eapply Forall_forall. intros a Ha.
    eapply in_map_iff in Ha. destruct Ha as (c & <- & Hc).
    eapply forallb_forall in H; [| exact Hc ]. unfold mk_alt.
    destruct (T ! c) as [[[code wc] n] |] eqn:HT; [| discriminate ].
    apply andb_true_iff in H. destruct H as [Hnd Hdis].
    split; [ rewrite fresh_vars_length; exact HT | split; [ eapply nodupb_spec; eassumption |] ].
    eapply forallb_disjoint; [| exact Hdis ].
    intros z Hz Hin. apply orb_false_iff in Hz. destruct Hz as [Hz1 Hz2].
    destruct Hin as [z Hin | z Hin]; [ eapply HS; eassumption | eapply in_code_false; eassumption ].
  Qed.

  Lemma sel_w_false w : sel_w w = false -> exposedb w = false.
  Proof. unfold sel_w. intros H. apply keeps_internal in H. apply H. Qed.

  Lemma dfn_ok_trans :
    (forall e, dfn_ok e = true -> trans L T Btop e (dfn e)) /\
    (forall B, forall rs0, dfn_ok_fd rs0 B = true -> trans_bundle L T Btop rs0 B (dfn_fd rs0 B) (recs_of B)).
  Proof.
    eapply exp_fundefs_ind.
    - (* Econstr *)
      intros x w t ys e IH H. simpl in H. apply andb_true_iff in H. destruct H as [Hx H].
      constructor; [ eapply in_code_false; apply negb_true_iff; eassumption | eauto ].
    - (* Ecase [] *) intros. constructor.
    - (* Ecase (_ :: _) *)
      intros x w cl c e IHe IHcl H. simpl in H. apply andb_true_iff in H. destruct H as [He Hcl].
      constructor; eauto.
    - (* Eproj *)
      intros x w t n y e IH H. simpl in H. apply andb_true_iff in H. destruct H as [Hx H].
      constructor; [ eapply in_code_false; apply negb_true_iff; eassumption | eauto ].
    - (* Eletapp *)
      intros x f w ys e IH H. simpl in H. simpl.
      apply andb_true_iff in H. destruct H as [H Hsel]. apply andb_true_iff in H. destruct H as [Hx Hk].
      apply negb_true_iff in Hx. specialize (IH Hk).
      destruct (sel_w w) eqn:Hw; simpl in Hsel.
      + constructor; [ exact Hw | eapply in_code_false; eassumption | exact IH ].
      + pose proof (sel_w_false w Hw) as Hwi.
        destruct (Nat.leb (esize e) thr).
        * econstructor; [ eassumption | eapply in_code_false; eassumption | | eassumption ].
          eapply alts_okb_spec; [| eassumption ].
          intros z Hz Hc. apply orb_false_iff in Hz. destruct Hz as [Hz Hz3]. apply orb_false_iff in Hz.
          destruct Hz as [Hz1 Hz2]. destruct Hc as [z Hc | z Hc]; [ destruct Hc as [z Hc | z Hc] |].
          -- inv Hc. rewrite Pos.eqb_refl in Hz1. discriminate.
          -- eapply memb_false; eassumption.
          -- eapply is_free_false; eassumption.
        * repeat match goal with
                 | [ H : (_ && _) = true |- _ ] => apply andb_true_iff in H; destruct H
                 end.
          repeat match goal with
                 | [ H : negb _ = true |- _ ] => apply negb_true_iff in H
                 end.
          econstructor; try eassumption.
          -- eapply in_code_false; eassumption.
          -- reflexivity.
          -- eapply in_code_false; eassumption.
          -- intros Hc; subst. rewrite Pos.eqb_refl in *. discriminate.
          -- intros Hc; subst. rewrite Pos.eqb_refl in *. discriminate.
          -- eapply memb_false; eassumption.
          -- eapply is_free_false; eassumption.
          -- eapply alts_okb_spec; [| eassumption ].
             intros z Hz Hc. apply orb_false_iff in Hz. destruct Hz as [Hz Hz3]. apply orb_false_iff in Hz.
             destruct Hz as [Hz1 Hz2]. destruct Hc as [z Hc | z Hc]; [ destruct Hc as [z Hc | z Hc] |].
             ++ inv Hc. rewrite Pos.eqb_refl in Hz1. discriminate.
             ++ eapply memb_false; eassumption.
             ++ inv Hc. rewrite Pos.eqb_refl in Hz3. discriminate.
    - (* Efun *)
      intros B e IHB IHe H. simpl in H. simpl.
      repeat match goal with
             | [ H : (_ && _) = true |- _ ] => apply andb_true_iff in H; destruct H
             end.
      econstructor.
      + eapply IHB. eassumption.
      + rewrite <- bnames_fnames. eapply nodupb_spec. eassumption.
      + eapply Disjoint_Included_l; [ intros z Hz; eapply name_in_bnames; exact Hz |].
        constructor. intros z Hz. destruct Hz as [z Hz1 Hz2].
        match goal with
        | [ Hf : forallb (fun f => negb (in_code f)) (bnames B) = true |- _ ] =>
            eapply forallb_forall in Hf; [| exact Hz1 ]; apply negb_true_iff in Hf;
            eapply in_code_false; eassumption
        end.
      + eapply (forallb_disjoint _ _ (fun z => memb z (rec_names (recs_of B)))); [| eassumption ]. intros z Hz. eapply memb_false. exact Hz.
      + eapply IHe. eassumption.
    - (* Eapp *)
      intros f w ys H. simpl in H. simpl.
      destruct (sel_w w) eqn:Hw; simpl in H.
      + constructor. exact Hw.
      + econstructor; [ eapply sel_w_false; eassumption |].
        eapply alts_okb_spec; [| eassumption ].
        intros z Hz Hc. apply orb_false_iff in Hz. destruct Hz as [Hz1 Hz2].
        destruct Hc as [z Hc | z Hc].
        * inv Hc. rewrite Pos.eqb_refl in Hz1. discriminate.
        * eapply memb_false; eassumption.
    - (* Eprim_val *) intros. constructor.
    - (* Eprim *) intros. constructor.
    - (* Ehalt *) intros. constructor.
    - (* Fcons *)
      intros f w xs e B IHe IHB rs0 H. simpl in H. simpl.
      apply andb_true_iff in H. destruct H as [Hf HB].
      destruct (sel_w w) eqn:Hw.
      + apply andb_true_iff in Hf. destruct Hf as [Hxs He].
        constructor; [ exact Hw | | eauto | eauto ].
        eapply forallb_disjoint; [| exact Hxs ].
        intros z Hz Hc. apply orb_false_iff in Hz. destruct Hz as [Hz Hz3]. apply orb_false_iff in Hz.
        destruct Hz as [Hz1 Hz2].
        destruct Hc as [z Hc | z Hc]; [ destruct Hc as [z Hc | z Hc] |].
        * exact (in_code_false z Hz1 Hc).
        * exact (memb_false z _ Hz2 Hc).
        * exact (memb_false z _ Hz3 Hc).
      + unfold wrapper_okb in Hf.
        destruct (wrapper_fields xs e) as [[[code wc] zs] |] eqn:Hwf; [| discriminate ].
        destruct (tagof ! f) as [c |] eqn:Htag; [| discriminate ].
        destruct (WM.get w L) as [lams |] eqn:HL; [| discriminate ].
        destruct (T ! c) as [[[code' wc'] n] |] eqn:HT; [| repeat (rewrite andb_false_r in Hf || rewrite andb_false_l in Hf); discriminate ].
        repeat match goal with
               | [ H : (_ && _) = true |- _ ] => apply andb_true_iff in H; destruct H
               end.
        repeat match goal with
               | [ H : negb _ = true |- _ ] => apply negb_true_iff in H
               end.
        apply Pos.eqb_eq in H6. apply web_eqb_eq in H8. apply Nat.eqb_eq in H7. subst code' wc' n.
        rewrite (wrapper_fields_spec _ _ _ _ _ Hwf).
        econstructor; eauto.
        * eapply sel_w_false; eassumption.
        * eapply memb_spec; eassumption.
        * eapply in_code_true; eassumption.
        * unfold sel_L in H3. destruct (WM.get wc L); [ discriminate | reflexivity ].
        * eapply nodupb_spec; eassumption.
        * eapply (forallb_disjoint _ _ (fun z => memb z zs)); [| eassumption ]. intros z Hz. eapply memb_false. exact Hz.
        * eapply memb_false; eassumption.
    - (* Fnil *) intros. constructor.
  Qed.

End Transform.

(** * The analysis *)

(** The functions defined in an expression *)
Fixpoint funs_of (e : exp) : list (var * web * list var * exp) :=
  match e with
  | Econstr _ _ _ _ k | Eproj _ _ _ _ _ k | Eletapp _ _ _ _ k => funs_of k
  | Ecase _ _ cl =>
      (fix go (cl : list (ctor_tag * exp)) :=
         match cl with
         | [] => []
         | (_, e) :: cl => funs_of e ++ go cl
         end) cl
  | Efun B k => funs_of_fd B ++ funs_of k
  | Eapp _ _ _ | Eprim_val _ _ _ | Eprim _ _ _ _ | Ehalt _ => []
  end
with funs_of_fd (B : fundefs) : list (var * web * list var * exp) :=
  match B with
  | Fcons f w xs e B => (f, w, xs, e) :: funs_of e ++ funs_of_fd B
  | Fnil => []
  end.

Fixpoint fd_bodies (B : fundefs) : list exp :=
  match B with
  | Fcons _ _ _ e B => e :: fd_bodies B
  | Fnil => []
  end.

Fixpoint fd_webs (B : fundefs) : list web :=
  match B with
  | Fcons _ w _ _ B => w :: fd_webs B
  | Fnil => []
  end.

Definition max_pos (l : list positive) : positive := fold_left Pos.max l 1%positive.

Record dfn_result : Type :=
  { r_L : WM.t (list ctor_tag);
    r_T : M.t (var * web * nat);
    r_tagof : M.t ctor_tag;
    r_cenv : term.ctor_env }.

Section Analysis.

  Variables (cenv : term.ctor_env) (Btop : fundefs) (e0 : exp).

  Definition inner_funs : list (var * web * list var * exp) :=
    concat (map funs_of (fd_bodies Btop)) ++ funs_of e0.

  Definition code_of (xs : list var) (e : exp) : option (var * web * list var) :=
    match wrapper_fields xs e with
    | Some (code, wc, zs) => if in_code Btop code then Some (code, wc, zs) else None
    | None => None
    end.

  (** The webs that cannot be defunctionalized *)
  Definition bad : WM.t unit :=
    let bad0 := fold_left (fun acc w => WM.set w tt acc) (fd_webs Btop) (WM.empty unit) in
    fold_left (fun acc '(f, w, xs, e) =>
                 match code_of xs e with
                 | Some (_, wc, _) => if exposedb w then WM.set w tt (WM.set wc tt acc) else WM.set wc tt acc
                 | None => WM.set w tt acc
                 end) inner_funs bad0.

  Definition is_bad (w : web) : bool := match WM.get w bad with Some _ => true | None => false end.

  Definition tag_base : positive := Pos.succ (max_pos (map fst (M.elements cenv))).
  Definition ind_base : positive := Pos.succ (max_pos (map (fun p => term.ctor_ind_tag (snd p)) (M.elements cenv))).

  (** Tags of the wrappers, lambda sets, and the table of code functions *)
  Definition assign : M.t ctor_tag * WM.t (list ctor_tag) * M.t (var * web * nat) * positive :=
    fold_left (fun '(tagof, L, T, c) '(f, w, xs, e) =>
                 if is_bad w then (tagof, L, T, c)
                 else match tagof ! f, code_of xs e with
                      | None, Some (code, wc, zs) =>
                          (M.set f c tagof,
                           WM.set w (match WM.get w L with Some lams => lams ++ [c] | None => [c] end) L,
                           M.set c (code, wc, length zs) T,
                           Pos.succ c)
                      | _, _ => (tagof, L, T, c)
                      end) inner_funs (M.empty _, WM.empty _, M.empty _, tag_base).

  (** One fresh inductive type per selected web *)
  Definition new_ctors : list (ctor_tag * term.ctor_ty_info) :=
    let '(_, L, T, _) := assign in
    fst (fold_left (fun '(acc, it) '(w, lams) =>
                      (acc ++ map (fun '(i, c) =>
                                     (c, {| term.ctor_name := BasicAst.nAnon;
                                            term.ctor_ind_name := BasicAst.nAnon;
                                            term.ctor_ind_tag := it;
                                            term.ctor_arity := match T ! c with
                                                               | Some (_, _, n) => N.of_nat n
                                                               | None => 0%N
                                                               end;
                                            term.ctor_ordinal := N.of_nat i |}))
                                  (combine (seq 0 (length lams)) lams),
                       Pos.succ it)) (WM_elements L) ([], ind_base)).

  Definition analyze_dfn : dfn_result :=
    let '(tagof, L, T, _) := assign in
    {| r_L := L; r_T := T; r_tagof := tagof;
       r_cenv := fold_left (fun acc '(c, info) => M.set c info acc) new_ctors cenv |}.

End Analysis.

Lemma r_cenv_eq cenv Btop e0 :
  r_cenv (analyze_dfn cenv Btop e0) =
  fold_left (fun acc '(c, info) => M.set c info acc) (new_ctors cenv Btop e0) cenv.
Proof. unfold analyze_dfn. destruct (assign cenv Btop e0) as [[[? ?] ?] ?]. reflexivity. Qed.

(** ** Checks of the hypotheses of the correctness theorem *)

Definition hl_check (cenv : term.ctor_env) (L : WM.t (list ctor_tag)) : bool :=
  forallb (fun '(w, lams) =>
             match lams with
             | [] => true
             | c0 :: _ =>
                 match cenv ! c0 with
                 | Some i0 =>
                     forallb (fun c => match cenv ! c with
                                       | Some i => Pos.eqb (term.ctor_ind_tag i) (term.ctor_ind_tag i0)
                                       | None => false
                                       end) lams
                 | None => false
                 end
             end) (WM_elements L).

Lemma hl_check_spec cenv L :
  hl_check cenv L = true ->
  forall w lams, WM.get w L = Some lams ->
                 exists it, Forall (fun c => exists info, M.get c cenv = Some info /\
                                                          term.ctor_ind_tag info = it) lams.
Proof.
  intros H w lams HL. eapply WM_elements_correct in HL.
  eapply forallb_forall in H; [| exact HL ]. simpl in H.
  destruct lams as [| c0 lams]; [ exists 1%positive; constructor |].
  destruct (cenv ! c0) as [i0 |] eqn:Hc0; [| discriminate ].
  exists (term.ctor_ind_tag i0). eapply Forall_forall. intros c Hc.
  eapply forallb_forall in H; [| exact Hc ].
  destruct (cenv ! c) as [i |]; [| discriminate ]. apply Pos.eqb_eq in H. eauto.
Qed.

Definition ht_check (Btop : fundefs) (T : M.t (var * web * nat)) : bool :=
  forallb (fun '(c, (code, wc, n)) => in_code Btop code) (M.elements T).

Lemma ht_check_spec Btop T :
  ht_check Btop T = true -> forall c code wc n, T ! c = Some (code, wc, n) -> Code Btop code.
Proof.
  intros H c code wc n HT. eapply M.elements_correct in HT.
  eapply forallb_forall in H; [| exact HT ]. simpl in H. eapply in_code_true; eassumption.
Qed.

(** The new constructors are new *)
Definition ext_check (cenv : term.ctor_env) (l : list (ctor_tag * term.ctor_ty_info)) : bool :=
  forallb (fun '(c, _) => match cenv ! c with None => true | Some _ => false end) l.

Lemma ext_check_spec cenv l :
  ext_check cenv l = true ->
  forall c i, cenv ! c = Some i -> (fold_left (fun acc '(c, info) => M.set c info acc) l cenv) ! c = Some i.
Proof.
  intros H c i Hc.
  assert (Hgen : forall acc, acc ! c = Some i ->
                             (fold_left (fun acc '(c, info) => M.set c info acc) l acc) ! c = Some i).
  { induction l as [| [c' info] l IH]; intros acc Hacc; simpl in *; eauto.
    apply andb_true_iff in H. destruct H as [H1 H2].
    eapply IH; [ exact H2 |]. rewrite M.gso; [ eassumption |].
    intros ->. rewrite Hc in H1. discriminate. }
  eapply Hgen. eassumption.
Qed.

(** * The implementation *)

Definition dfn_thr : nat := 10.

(** The largest index of an internal web of a program: the join points get a
    fresh internal web above it. *)
Definition iweb (w : web) : positive := match w with Internal p => p | Exposed _ => 1%positive end.

Fixpoint max_iweb (e : exp) : positive :=
  match e with
  | Econstr _ w _ _ k | Eproj _ w _ _ _ k | Eletapp _ _ w _ k => Pos.max (iweb w) (max_iweb k)
  | Ecase _ w cl =>
      (fix go (cl : list (ctor_tag * exp)) :=
         match cl with
         | [] => iweb w
         | (_, e) :: cl => Pos.max (max_iweb e) (go cl)
         end) cl
  | Efun B k => Pos.max (max_iweb_fd B) (max_iweb k)
  | Eapp _ w _ => iweb w
  | Eprim_val _ _ k | Eprim _ _ _ k => max_iweb k
  | Ehalt _ => 1%positive
  end
with max_iweb_fd (B : fundefs) : positive :=
  match B with
  | Fcons _ w _ e B => Pos.max (iweb w) (Pos.max (max_iweb e) (max_iweb_fd B))
  | Fnil => 1%positive
  end.

Definition dfn_top (cenv : term.ctor_env) (e : exp) : term.ctor_env * exp :=
  match e with
  | Efun Btop e0 =>
      let r := analyze_dfn cenv Btop e0 in
      let L := r_L r in
      let T := r_T r in
      let tagof := r_tagof r in
      let m := identifiers.max_var (erase e) 1%positive in
      let jw := Pos.succ (max_iweb e) in
      if forallb (sel_w L) (fd_webs Btop) && nodupb (bnames Btop) &&
         dfn_ok_fd L T Btop tagof m dfn_thr [] Btop && dfn_ok L T Btop tagof m dfn_thr e0 &&
         hl_check (r_cenv r) L && ht_check Btop T && ext_check cenv (new_ctors cenv Btop e0)
      then (r_cenv r, Efun (dfn_fd L T tagof m dfn_thr jw [] Btop) (dfn L T tagof m dfn_thr jw e0))
      else (cenv, e)
  | _ => (cenv, e)
  end.

(** * Correctness *)

Lemma recs_of_keep L tagof B :
  forallb (sel_w L) (fd_webs B) = true -> recs_of L tagof B = [].
Proof.
  induction B; simpl; intros H; eauto. apply andb_true_iff in H. destruct H as [H1 H2].
  rewrite H1. eauto.
Qed.

Lemma caseConsistent_ext cenv cenv' cl c :
  (forall c i, cenv ! c = Some i -> cenv' ! c = Some i) ->
  term_util.caseConsistent cenv cl c -> term_util.caseConsistent cenv' cl c.
Proof. intros Hext H. induction H; econstructor; eauto. Qed.

Lemma bstep_cenv_ext cenv cenv' ex rho e c r t :
  (forall c i, cenv ! c = Some i -> cenv' ! c = Some i) ->
  bstep_fuel cenv ex rho e c r t -> bstep_fuel cenv' ex rho e c r t.
Proof.
  intros Hext H.
  eapply (@bstep_fuel_ind' cenv _ _ _ _
            (fun ex rho e c r t => bstep cenv' ex rho e c r t)
            (fun ex rho e c r t => bstep_fuel cenv' ex rho e c r t)); eauto;
    intros; try (econstructor; eauto; fail).
  econstructor; eauto. eapply caseConsistent_ext; eauto.
Qed.

Lemma value_ref_refl v : value_ref v v.
Proof.
  induction v using val_ind_Forall; simpl; eauto.
  split; eauto. split; eauto. induction H; constructor; eauto. rewrite value_ref_eq. eauto.
Qed.

(** The output refines the input: the input is evaluated with the original
    constructor environment, and the output with the extended one. *)
Theorem dfn_top_refines cenv e :
  closed_exp e ->
  let '(cenv', et) := dfn_top cenv e in
  (forall v1 c1 t1, bstep_fuel cenv true emp e c1 (Res v1) t1 ->
                    exists v2 c2 t2, bstep_fuel cenv' true emp et c2 (Res v2) t2 /\ value_ref v1 v2) /\
  (diverge cenv true emp e -> diverge cenv' true emp et).
Proof.
  intros Hc. unfold dfn_top.
  assert (Hid : forall e, (forall v1 c1 t1, bstep_fuel cenv true emp e c1 (Res v1) t1 ->
                                            exists v2 c2 t2, bstep_fuel cenv true emp e c2 (Res v2) t2 /\ value_ref v1 v2) /\
                          (diverge cenv true emp e -> diverge cenv true emp e)).
  { intros e'. split; eauto. intros. do 3 eexists. split; [ eassumption | eapply value_ref_refl ]. }
  destruct e; eauto.
  match goal with
  | [ |- context [ if ?b then _ else _ ] ] => destruct b eqn:Hchk; [| eapply Hid ]
  end.
  repeat match goal with
         | [ H : (_ && _) = true |- _ ] => apply andb_true_iff in H; destruct H
         end.
  set (r := analyze_dfn cenv f e) in *.
  set (m := identifiers.max_var (erase (Efun f e)) 1%positive) in *.
  set (jw := Pos.succ (max_iweb (Efun f e))) in *.
  assert (Hext : forall c i, cenv ! c = Some i -> (r_cenv r) ! c = Some i).
  { intros c i Hci. unfold r. rewrite r_cenv_eq. eapply ext_check_spec; eauto. }
  assert (Htop : trans_top (r_L r) (r_T r) f (Efun f e)
                           (Efun (dfn_fd (r_L r) (r_T r) (r_tagof r) m dfn_thr jw [] f)
                                 (dfn (r_L r) (r_T r) (r_tagof r) m dfn_thr jw e))).
  { do 3 eexists. split; [ reflexivity | split; [ reflexivity |] ].
    split; [| split ].
    - match goal with
      | [ Hk : forallb (sel_w _) (fd_webs f) = true, Hfd : dfn_ok_fd _ _ _ _ _ _ [] f = true |- _ ] =>
          pose proof (proj2 (dfn_ok_trans _ _ _ _ _ _ jw) f [] Hfd) as Hb;
          rewrite (recs_of_keep _ _ _ Hk) in Hb; exact Hb
      end.
    - rewrite <- bnames_fnames. eapply nodupb_spec. eassumption.
    - eapply (proj1 (dfn_ok_trans _ _ _ _ _ _ jw)). eassumption. }
  pose proof (dfn_refines (r_cenv r) (fuel := nat) (trace := nat * nat) (r_L r) (r_T r) f
                          (hl_check_spec _ _ ltac:(eassumption)) (ht_check_spec _ _ ltac:(eassumption))
                          _ _ Hc Htop) as [Hterm Hdiv].
  split.
  - intros v1 c1 t1 Hs. eapply Hterm. eapply bstep_cenv_ext; eassumption.
  - intros Hd. eapply Hdiv. intros c1. destruct (Hd c1) as [t1 Ht1]. eexists. eapply bstep_cenv_ext; eassumption.
Qed.
