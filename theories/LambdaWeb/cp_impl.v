(* An implementation of constant propagation with local constants and
   dead-binding elimination, and the proof that it inhabits the relation of
   cp.v.

   - The transformation [cp] follows the relation: it tracks the scoped
     environment of the local constants, drops the constant arguments of
     the calls of the webs in the map, binds the constant parameters on
     entry, and drops dead [Econstr], [Eproj] and [Efun] bindings.
   - The checker [cp_ok] checks the side conditions of the relation (every
     constant argument is a known constant; the transformed functions have
     distinct parameters and the right arity).  It is proven sound.
   - The analysis [analyze] computes, for every internal web, the constants
     passed at each position by all the calls of the web.  Constant
     parameters of the enclosing functions are known constants, so the
     analysis is iterated; it is not proven correct: the top level uses the
     most precise result that the checker accepts, and otherwise transforms
     no web (only removes dead bindings), which the checker always accepts. *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics set_util.
From CertiRocq.LambdaWeb Require Import syntax semantics exposed post select indep bound comp dpe cp dpe_impl.
From CertiRocq.LambdaWeb Require fixpoint.

Import ListNotations.

(** * Decision procedures *)

Fixpoint nodupb (xs : list var) : bool :=
  match xs with
  | [] => true
  | x :: xs => negb (existsb (Pos.eqb x) xs) && nodupb xs
  end.

Lemma nodupb_spec xs : nodupb xs = true -> NoDup xs.
Proof.
  induction xs as [| x xs IH]; simpl; intros H; constructor.
  - apply andb_true_iff in H. destruct H as [H _]. intros Hc.
    apply negb_true_iff in H. assert (Hc' : existsb (Pos.eqb x) xs = true).
    { eapply existsb_exists. exists x. split; [ eassumption | apply Pos.eqb_refl ]. }
    congruence.
  - apply andb_true_iff in H. eapply IH. apply H.
Qed.

Definition const_info_eqb (i j : const_info) : bool :=
  let '(c, w) := i in let '(c', w') := j in Pos.eqb c c' && web_eqb w w'.

Lemma const_info_eqb_spec i j : const_info_eqb i j = true -> i = j.
Proof.
  destruct i as [c w], j as [c' w']. simpl. intros H. apply andb_true_iff in H.
  destruct H as [H1 H2]. apply Pos.eqb_eq in H1; apply web_eqb_eq in H2. subst. reflexivity.
Qed.

Fixpoint const_okb (K : M.t const_info) (ys : list var) (cs : list (option const_info)) : bool :=
  match ys, cs with
  | y :: ys', Some i :: cs' =>
      match K ! y with Some j => const_info_eqb j i | None => false end && const_okb K ys' cs'
  | _ :: ys', None :: cs' => const_okb K ys' cs'
  | _, _ => true
  end.

Lemma const_okb_spec K ys cs : const_okb K ys cs = true -> const_ok K ys cs.
Proof.
  revert cs; induction ys as [| y ys IH]; intros [| [i |] cs] H; simpl in *; eauto.
  apply andb_true_iff in H. destruct H as [H1 H2]. split; eauto.
  destruct (K ! y) as [j |]; [| discriminate ]. f_equal. eapply const_info_eqb_spec; eassumption.
Qed.

(** * The transformation and its checker *)

Section Transform.

  Variable (Lc : WM.t (list (option const_info))).

  Definition cp_cs (w : web) : list (option const_info) :=
    match WM.get w Lc with Some cs => cs | None => [] end.

  Definition cp_args {A} (w : web) (ys : list A) : list A :=
    if keeps (sel_L Lc) w then ys else live_args ys (cmask (cp_cs w)).

  (** The constant environment after the binding of [x] by an [Econstr] *)
  Definition constr_env (K : M.t const_info) (x : var) (w : web) (t : ctor_tag) (ys : list var) :=
    match ys with [] => M.set x (t, w) K | _ => M.remove x K end.

  Fixpoint cp (K : M.t const_info) (e : exp) : exp :=
    match e with
    | Econstr x w t ys k =>
        let k' := cp (constr_env K x w t ys) k in
        if is_free k' x then Econstr x w t ys k' else k'
    | Eproj x w t n y k =>
        let k' := cp (M.remove x K) k in if is_free k' x then Eproj x w t n y k' else k'
    | Ecase x w cl =>
        Ecase x w ((fix go (cl : list (ctor_tag * exp)) :=
                      match cl with
                      | [] => []
                      | (c, e) :: cl => (c, cp K e) :: go cl
                      end) cl)
    | Eletapp x f w ys k => Eletapp x f w (cp_args w ys) (cp (M.remove x K) k)
    | Efun B k =>
        let K' := remove_fnames B K in
        let k' := cp K' k in
        if existsb (is_free k') (bnames B) then Efun (cp_fd K' B) k' else k'
    | Eapp f w ys => Eapp f w (cp_args w ys)
    | Eprim_val x p k => Eprim_val x p (cp (M.remove x K) k)
    | Eprim x p ys k => Eprim x p ys (cp (M.remove x K) k)
    | Ehalt x => Ehalt x
    end
  with cp_fd (K : M.t const_info) (B : fundefs) : fundefs :=
    match B with
    | Fcons f w xs e B =>
        if keeps (sel_L Lc) w then Fcons f w xs (cp (param_consts xs [] K) e) (cp_fd K B)
        else Fcons f w (live_args xs (cmask (cp_cs w)))
                   (bind_consts xs (cp_cs w) (cp (param_consts xs (cp_cs w) K) e)) (cp_fd K B)
    | Fnil => Fnil
    end.

  Fixpoint cp_ok (K : M.t const_info) (e : exp) : bool :=
    match e with
    | Econstr x w t ys k => cp_ok (constr_env K x w t ys) k
    | Eproj x w t n y k => cp_ok (M.remove x K) k
    | Ecase x w cl =>
        (fix go (cl : list (ctor_tag * exp)) :=
           match cl with
           | [] => true
           | (c, e) :: cl => cp_ok K e && go cl
           end) cl
    | Eletapp x f w ys k =>
        (keeps (sel_L Lc) w || const_okb K ys (cp_cs w)) && cp_ok (M.remove x K) k
    | Efun B k => cp_ok_fd (remove_fnames B K) B && cp_ok (remove_fnames B K) k
    | Eapp f w ys => keeps (sel_L Lc) w || const_okb K ys (cp_cs w)
    | Eprim_val x _ k | Eprim x _ _ k => cp_ok (M.remove x K) k
    | Ehalt _ => true
    end
  with cp_ok_fd (K : M.t const_info) (B : fundefs) : bool :=
    match B with
    | Fcons f w xs e B =>
        (if keeps (sel_L Lc) w then cp_ok (param_consts xs [] K) e
         else Nat.eqb (length (cp_cs w)) (length xs) && nodupb xs &&
              cp_ok (param_consts xs (cp_cs w) K) e) && cp_ok_fd K B
    | Fnil => true
    end.

  (** ** Soundness of the checker *)

  Variable (Gb : nat).

  Lemma cp_cs_sel w : keeps (sel_L Lc) w = false -> exposedb w = false /\ WM.get w Lc = Some (cp_cs w).
  Proof.
    intros H. apply keeps_internal in H. destruct H as [Hw Hs]. split; [ eassumption |].
    unfold sel_L, cp_cs in *. destruct (WM.get w Lc); congruence.
  Qed.

  Lemma cp_trans :
    (forall e K, cp_ok K e = true -> esize e <= Gb -> trans Lc Gb K (esize e) e (cp K e)) /\
    (forall B K, cp_ok_fd K B = true -> fsize B <= Gb -> trans_fundefs Lc Gb K B (cp_fd K B)).
  Proof.
    eapply exp_fundefs_ind.
    - (* Econstr *)
      intros x w t ys e IH K Hok Hs. simpl in *.
      specialize (IH _ Hok ltac:(lia)).
      destruct ys as [| y ys]; simpl in *;
        (destruct (is_free (cp _ e) x) eqn:Hx;
         [ constructor; eapply trans_weaken; [ eassumption | lia ]
         | econstructor; [ eassumption | lia | eapply is_free_false; eassumption ] ]).
    - (* Ecase [] *)
      intros. constructor.
    - (* Ecase (_ :: _) *)
      intros x w cl c e IHe IHcl K Hok Hs. simpl in *. apply andb_true_iff in Hok. destruct Hok as [Hoke Hokcl].
      constructor.
      + eapply trans_weaken; [ eapply IHe; [ eassumption | lia ] | lia ].
      + eapply trans_weaken; [ eapply IHcl; [ eassumption | simpl; lia ] | simpl; lia ].
    - (* Eproj *)
      intros x w t n y e IH K Hok Hs. simpl in *.
      specialize (IH _ Hok ltac:(lia)).
      destruct (is_free (cp _ e) x) eqn:Hx.
      + constructor. eapply trans_weaken; [ eassumption | lia ].
      + econstructor; [ eassumption | lia | eapply is_free_false; eassumption ].
    - (* Eletapp *)
      intros x f w ys e IH K Hok Hs. simpl in *. apply andb_true_iff in Hok. destruct Hok as [Hcall Hok].
      specialize (IH _ Hok ltac:(lia)). unfold cp_args.
      destruct (keeps (sel_L Lc) w) eqn:Hk.
      + constructor; [ eassumption | eapply trans_weaken; [ eassumption | lia ] ].
      + destruct (cp_cs_sel w Hk) as [Hw HL]. simpl in Hcall.
        econstructor; [ eassumption | eassumption | eapply const_okb_spec; eassumption
                      | eapply trans_weaken; [ eassumption | lia ] ].
    - (* Efun *)
      intros B e IHB IHe K Hok Hs. simpl in *. apply andb_true_iff in Hok. destruct Hok as [HokB Hoke].
      specialize (IHe _ Hoke ltac:(lia)). specialize (IHB _ HokB ltac:(lia)).
      destruct (existsb (is_free (cp (remove_fnames B K) e)) (bnames B)) eqn:Hb.
      + constructor; [ eassumption | eapply trans_weaken; [ eassumption | lia ] ].
      + econstructor; [ eassumption | lia |].
        constructor. intros z Hz. destruct Hz as [z Hz1 Hz2].
        eapply is_free_spec in Hz2.
        assert (Hc : existsb (is_free (cp (remove_fnames B K) e)) (bnames B) = true).
        { eapply existsb_exists. eexists; split; [ eapply name_in_bnames; eassumption | eassumption ]. }
        congruence.
    - (* Eapp *)
      intros f w ys K Hok Hs. simpl in *. unfold cp_args.
      destruct (keeps (sel_L Lc) w) eqn:Hk.
      + constructor; eassumption.
      + destruct (cp_cs_sel w Hk) as [Hw HL]. simpl in Hok.
        econstructor; [ eassumption | eassumption | eapply const_okb_spec; eassumption ].
    - (* Eprim_val *)
      intros x p e IH K Hok Hs. simpl in *. constructor.
      eapply trans_weaken; [ eapply IH; [ eassumption | lia ] | lia ].
    - (* Eprim *)
      intros x p ys e IH K Hok Hs. simpl in *. constructor.
      eapply trans_weaken; [ eapply IH; [ eassumption | lia ] | lia ].
    - (* Ehalt *) intros. constructor.
    - (* Fcons *)
      intros f w xs e B IHe IHB K Hok Hs. simpl in *. apply andb_true_iff in Hok. destruct Hok as [Hokf HokB].
      specialize (IHB _ HokB ltac:(lia)).
      destruct (keeps (sel_L Lc) w) eqn:Hk.
      + constructor; [ eassumption | eapply trans_weaken; [ eapply IHe; [ eassumption | lia ] | lia ] | eassumption ].
      + destruct (cp_cs_sel w Hk) as [Hw HL].
        apply andb_true_iff in Hokf. destruct Hokf as [Hokf Hoke]. apply andb_true_iff in Hokf.
        destruct Hokf as [Hlen Hnd]. apply Nat.eqb_eq in Hlen.
        econstructor; [ eassumption | eassumption | eassumption | eapply nodupb_spec; eassumption
                      | eapply trans_weaken; [ eapply IHe; [ eassumption | lia ] | lia ] | eassumption ].
    - (* Fnil *) intros. constructor.
  Qed.

End Transform.

(** With no selected web, the checker always succeeds. *)
Lemma cp_ok_empty :
  (forall e K, cp_ok (WM.empty _) K e = true) /\ (forall B K, cp_ok_fd (WM.empty _) K B = true).
Proof.
  assert (Hk : forall w, keeps (sel_L (WM.empty (list (option const_info)))) w = true).
  { intros w. unfold keeps, sel_L. rewrite WM.gempty. apply orb_true_r. }
  eapply exp_fundefs_ind; simpl; intros; rewrite ?Hk; simpl;
    repeat match goal with
           | [ IH : forall K, ?g K ?x = true |- context [ ?g ?K' ?x ] ] => rewrite IH
           end; eauto.
Qed.

(** * The analysis *)

Definition centry : Type := option (list (option const_info)).

Definition meet_ci (a b : option const_info) : option const_info :=
  match a, b with
  | Some i, Some j => if const_info_eqb i j then Some i else None
  | _, _ => None
  end.

Fixpoint meet_list (l1 l2 : list (option const_info)) : list (option const_info) :=
  match l1, l2 with
  | a :: l1, b :: l2 => meet_ci a b :: meet_list l1 l2
  | _, _ => []
  end.

Definition add_call (w : web) (info : list (option const_info)) (tbl : WM.t centry) : WM.t centry :=
  match WM.get w tbl with
  | None => WM.set w (Some info) tbl
  | Some None => tbl
  | Some (Some info') =>
      if Nat.eqb (length info') (length info) then WM.set w (Some (meet_list info' info)) tbl
      else WM.set w None tbl
  end.

(** Arity of the functions of a web; [None] if they disagree or have repeated parameters *)
Definition add_fun (w : web) (xs : list var) (tbl : WM.t (option nat)) : WM.t (option nat) :=
  if nodupb xs then
    match WM.get w tbl with
    | None => WM.set w (Some (length xs)) tbl
    | Some None => tbl
    | Some (Some n) => if Nat.eqb n (length xs) then tbl else WM.set w None tbl
    end
  else WM.set w None tbl.

Section Analysis.

  (** The constants of the previous round, for the parameters *)
  Variable (Lprev : WM.t (list (option const_info))).

  Definition prev_cs (w : web) : list (option const_info) :=
    if exposedb w then [] else match WM.get w Lprev with Some cs => cs | None => [] end.

  Definition tables : Type := (WM.t centry * WM.t (option nat))%type.

  Fixpoint collect_cp (K : M.t const_info) (e : exp) (t : tables) : tables :=
    match e with
    | Econstr x w c ys k => collect_cp (constr_env K x w c ys) k t
    | Eproj x _ _ _ _ k => collect_cp (M.remove x K) k t
    | Ecase _ _ cl =>
        (fix go (cl : list (ctor_tag * exp)) t :=
           match cl with
           | [] => t
           | (_, e) :: cl => go cl (collect_cp K e t)
           end) cl t
    | Eletapp x f w ys k =>
        let t := if exposedb w then t else (add_call w (map (fun y => K ! y) ys) (fst t), snd t) in
        collect_cp (M.remove x K) k t
    | Efun B k => collect_cp (remove_fnames B K) k (collect_cp_fd (remove_fnames B K) B t)
    | Eapp f w ys => if exposedb w then t else (add_call w (map (fun y => K ! y) ys) (fst t), snd t)
    | Eprim_val x _ k | Eprim x _ _ k => collect_cp (M.remove x K) k t
    | Ehalt _ => t
    end
  with collect_cp_fd (K : M.t const_info) (B : fundefs) (t : tables) : tables :=
    match B with
    | Fcons f w xs e B =>
        let t := if exposedb w then t else (fst t, add_fun w xs (snd t)) in
        collect_cp_fd K B (collect_cp (param_consts xs (prev_cs w) K) e t)
    | Fnil => t
    end.

  Definition analyze (e : exp) : WM.t (list (option const_info)) :=
    let '(calls, funs) := collect_cp (M.empty _) e (WM.empty _, WM.empty _) in
    M.map_filter1 (fun o => o)
      (M.map (fun p (ce : centry) => let w := web_of_index p in
                match ce, WM.get w funs with
                | Some cs, Some (Some n) =>
                    if Nat.eqb n (length cs) && negb (exposedb w) && existsb (fun o : option const_info => match o with Some _ => true | None => false end) cs then Some cs else None
                | _, _ => None
                end) calls).

End Analysis.

Fixpoint analyze_n (n : nat) (e : exp) : WM.t (list (option const_info)) :=
  match n with
  | 0 => WM.empty _
  | S n => analyze (analyze_n n e) e
  end.

(** The constants of the known-constructor fixpoint of [fixpoint.v]: a
    position is constant if it always receives the same nullary
    constructor *)
Definition cp_fix (e : exp) : list (WM.t (list (option const_info))) :=
  match fixpoint.param_cons e with
  | Some P =>
      [fold_left (fun Lc '(w, vs) =>
                    let cs := map (fun v => match v with
                                            | fixpoint.CCon wc c O => Some (c, wc)
                                            | _ => None
                                            end) vs in
                    if existsb (fun o : option const_info => match o with Some _ => true | None => false end) cs
                    then WM.set w cs Lc else Lc) (WM_elements P) (WM.empty _)]
  | None => []
  end.

(** The first map that the checker accepts: the fixpoint, or else the
    rounds of the local analysis *)
Definition choose_map (e : exp) : WM.t (list (option const_info)) :=
  let cands := cp_fix e ++ [analyze_n 3 e; analyze_n 2 e; analyze_n 1 e] in
  match find (fun Lc => cp_ok Lc (M.empty _) e) cands with
  | Some Lc => Lc
  | None => WM.empty _
  end.

Lemma choose_map_ok e : cp_ok (choose_map e) (M.empty _) e = true.
Proof.
  unfold choose_map.
  destruct (find (fun Lc => cp_ok Lc (M.empty _) e) _) eqn:Hf.
  - eapply find_some in Hf. apply Hf.
  - eapply cp_ok_empty.
Qed.

Definition cp_top (e : exp) : exp := cp (choose_map e) (M.empty _) e.

(** * Correctness of the implementation *)

Theorem cp_top_trans e : trans (choose_map e) (esize e) (M.empty _) (esize e) e (cp_top e).
Proof. eapply cp_trans; [ eapply choose_map_ok | lia ]. Qed.

Section Top.

  Variable (cenv : term.ctor_env).

  Theorem cp_top_refines e : closed_exp e -> refines cenv value_ref e (cp_top e).
  Proof. intros Hc. eapply cp_refines; [ eassumption | | eapply cp_top_trans ]. lia. Qed.

  Theorem cp_top_correct e :
    E_web cenv (dead_bound (esize e) (esize e)) (dead_bound (esize e) (esize e)) e (cp_top e).
  Proof.
    eapply (E_web_cp cenv (choose_map e) (esize e) (dead_bound (esize e) (esize e)) (fun n => dead_bound n (esize e)));
      [ eapply dead_bound_target_step | lia | eapply cp_top_trans ].
  Qed.

End Top.
