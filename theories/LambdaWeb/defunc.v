(* MLton-style defunctionalization on λweb.

   Every internal function is lifted to a closed top-level "code" function,
   and every internal closure is represented by a constructor value whose
   tag identifies the function and whose fields are the free variables of
   its bundle.  The web of a closure becomes the web of its record, and a
   call through an internal web [w] becomes a case analysis on the record
   over the lambda set of [w] (the tags of the functions that may flow to
   the call, as given by the flow analysis), followed by a direct call of
   the corresponding code function on the fields and the arguments.

     source                                target
     ------                                ------
                                           let rec code_f zs xs =
                                             let f = C_f(zs) in ... body'
     let rec f xs = body (* web w *)       let f = C_f(fvs) in        (* web w *)
     ... (f ys)_w ...                      ... case_w f of
                                                 | C_f(zs) => code_f (zs ++ ys)
                                                 | C_g(zs) => code_g (zs ++ ys) ...

   Exposed functions and calls are left in place (their bodies are
   transformed).  Bundles are either entirely exposed or entirely internal.
   Since mutually recursive siblings share their free variables, each code
   function rebuilds the records of its siblings from its own fields.

   The relation [VT_dfn] relates an internal closure to its record:
   applying the closure is related to applying the code function selected by
   the record's tag to the record's fields and the arguments.

   The target always takes at least as many steps as the source, so we work
   with postconditions that are insensitive to extra target steps
   ([post_target_steps]); [P_ge] ("the target uses at least as much fuel as
   the source") is such a postcondition, and it gives divergence
   preservation. *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics algebra set_util.
From CertiRocq.LambdaANF Require term term_util identifiers.
From CertiRocq.LambdaWeb Require Import syntax semantics exposed post compat indep comp.

Import ListNotations.

Open Scope alg_scope.

(** * Syntax of the transformation *)

(** The records of the functions of a bundle, built from the free variables
    [fvs] of the bundle. *)
Fixpoint bind_records (B : fundefs) (cs : list ctor_tag) (fvs : list var) (e : exp) : exp :=
  match B, cs with
  | Fcons f w _ _ B', c :: cs' => Econstr f w c fvs (bind_records B' cs' fvs e)
  | _, _ => e
  end.

(** Projecting the fields of a record *)
Fixpoint projs (zs : list var) (w : web) (c : ctor_tag) (n : N) (g : var) (e : exp) : exp :=
  match zs with
  | [] => e
  | z :: zs => Eproj z w c n g (projs zs w c (N.succ n) g e)
  end.

(** An alternative of a dispatch: the tag of a function, its code function,
    the web of the code function, and the variables receiving the fields. *)
Definition alt : Type := (ctor_tag * var * web * list var)%type.

Definition alt_tag (a : alt) : ctor_tag := let '(c, _, _, _) := a in c.

Definition dispatch (g : var) (w : web) (alts : list alt) (call : var -> web -> list var -> exp) : exp :=
  Ecase g w (map (fun '(c, code, wc, zs) => (c, projs zs w c 0 g (call code wc zs))) alts).

Fixpoint fnames (B : fundefs) : list var :=
  match B with
  | Fcons f _ _ _ B => f :: fnames B
  | Fnil => []
  end.

(** Webs and tags of the records of a bundle *)
Fixpoint rec_of (B : fundefs) (cs : list ctor_tag) (f : var) : option (web * ctor_tag) :=
  match B, cs with
  | Fcons g w _ _ B', c :: cs' => if M.elt_eq f g then Some (w, c) else rec_of B' cs' f
  | _, _ => None
  end.


Section Defunc.

  Variable (cenv : term.ctor_env).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Local Notation PostT := (@exposed.PostT fuel trace).
  Local Notation PostGT := (@exposed.PostGT fuel trace).
  Local Notation VTransT := (@exposed.VTransT fuel trace).

  (** ** Target-only evaluation steps *)

  Lemma bstep_fuel_ex_exposed ex rho e c r t :
    bstep_fuel cenv ex rho e c r t -> ex = true -> exposed_res r.
  Proof. intros H Hex; subst; eapply bstep_fuel_exposed; eauto. Qed.

  Lemma E_target_step (V : nat -> val -> val -> Prop) P ex k p1 e2 rho2 e2' rho2'
        (Hpt : post_target_steps P) :
    (forall cin r cout,
        bstep_fuel cenv ex rho2' e2' cin r cout ->
        exists cin' cout', bstep_fuel cenv ex rho2 e2 cin' r cout' /\ ge cin' cin /\ ge cout' cout) ->
    E' cenv V P ex k p1 (e2', rho2') -> E' cenv V P ex k p1 (e2, rho2).
  Proof.
    destruct p1 as [e1 rho1]. intros Hstep HE r1 cin cout Hleq Hs.
    edestruct HE as (r2 & cin2 & cout2 & Hs2 & HP & HR); eauto.
    edestruct Hstep as (cin' & cout' & Hs' & Hc & Ht'); eauto.
    do 3 eexists. split; [ eassumption | split; [ eapply Hpt; eauto | eassumption ] ].
  Qed.

  Lemma wrap_constr ex rho x w c ys vs e cin r cout :
    get_list ys rho = Some vs ->
    (exposedb w = true -> Forall exposed_val vs) ->
    bstep_fuel cenv ex (M.set x (Vconstr w c vs) rho) e cin r cout ->
    exists cin' cout', bstep_fuel cenv ex rho (Econstr x w c ys e) cin' r cout' /\ ge cin' cin /\ ge cout' cout.
  Proof.
    intros Hget Hexp Hs. do 2 eexists. split; [| split; eapply ge_plus_r ].
    econstructor 2; [ econstructor; eauto |]. eapply bstep_fuel_ex_exposed; eauto.
  Qed.

  Lemma wrap_proj ex rho x w c n y vs v e cin r cout :
    M.get y rho = Some (Vconstr w c vs) ->
    nthN vs n = Some v ->
    bstep_fuel cenv ex (M.set x v rho) e cin r cout ->
    exists cin' cout', bstep_fuel cenv ex rho (Eproj x w c n y e) cin' r cout' /\ ge cin' cin /\ ge cout' cout.
  Proof.
    intros Hget Hnth Hs. do 2 eexists. split; [| split; eapply ge_plus_r ].
    econstructor 2; [ econstructor; eauto |]. eapply bstep_fuel_ex_exposed; eauto.
  Qed.

  Lemma wrap_fun ex rho B e cin r cout :
    bstep_fuel cenv ex (def_funs B B rho rho) e cin r cout ->
    exists cin' cout', bstep_fuel cenv ex rho (Efun B e) cin' r cout' /\ ge cin' cin /\ ge cout' cout.
  Proof.
    intros Hs. do 2 eexists. split; [| split; eapply ge_plus_r ].
    econstructor 2; [ econstructor; eauto |]. eapply bstep_fuel_ex_exposed; eauto.
  Qed.

  Lemma wrap_case ex rho y w cl c vs e n cin r cout :
    M.get y rho = Some (Vconstr w c vs) ->
    term_util.caseConsistent cenv (erase_branches cl) c ->
    find_tag_nth cl c e n ->
    bstep_fuel cenv ex rho e cin r cout ->
    exists cin' cout', bstep_fuel cenv ex rho (Ecase y w cl) cin' r cout' /\ ge cin' cin /\ ge cout' cout.
  Proof.
    intros Hget Hcc Hft Hs. do 2 eexists. split; [| split; eapply ge_plus_r ].
    econstructor 2; [ econstructor; eauto |]. eapply bstep_fuel_ex_exposed; eauto.
  Qed.

  (** ** Projections of all the fields of a record *)

  Lemma nthN_app_middle {A} (pre ws : list A) w :
    nthN (pre ++ w :: ws) (N.of_nat (length pre)) = Some w.
  Proof.
    rewrite nthN_app_geq; [| lia ]. rewrite N.sub_diag. reflexivity.
  Qed.

  Lemma set_lists_cons_permut {A} (z : var) zs (v : A) vs rho rho' :
    ~ List.In z zs ->
    set_lists zs vs (M.set z v rho) = Some rho' ->
    set_lists (z :: zs) (v :: vs) rho = Some rho'.
  Proof.
    intros Hnin Hs. simpl.
    destruct (set_lists zs vs rho) as [rho'' |] eqn:Hs'.
    - edestruct (set_set_lists_permut rho rho'' z zs v vs Hs' Hnin) as (rho3 & Hs3 & Heq).
      rewrite Hs in Hs3. inv Hs3. f_equal. apply M.extensionality. intros i. rewrite Heq. reflexivity.
    - exfalso. apply set_lists_length_eq in Hs.
      destruct (set_lists_length3 rho zs vs Hs) as [rho5 Hs5]. congruence.
  Qed.

  Lemma E_projs_r_gen (V : nat -> val -> val -> Prop) P ex k p1 w c g e2
        (Hpt : post_target_steps P) :
    forall zs pre ws rho2,
      M.get g rho2 = Some (Vconstr w c (pre ++ ws)) ->
      NoDup zs -> ~ List.In g zs -> length zs = length ws ->
      (forall rho2', set_lists zs ws rho2 = Some rho2' -> E' cenv V P ex k p1 (e2, rho2')) ->
      E' cenv V P ex k p1 (projs zs w c (N.of_nat (length pre)) g e2, rho2).
  Proof.
    induction zs as [| z zs IH]; intros pre ws rho2 Hget Hnd Hnin Hlen Hk; simpl.
    - destruct ws; simpl in Hlen; try congruence. eapply Hk. reflexivity.
    - destruct ws as [| v ws]; simpl in Hlen; try congruence. inv Hnd.
      eapply E_target_step; [ eassumption | |].
      + intros. eapply wrap_proj; [ eassumption | eapply nthN_app_middle | eassumption ].
      + replace (N.succ (N.of_nat (length pre))) with (N.of_nat (length (pre ++ [v]))).
        2:{ rewrite length_app. simpl. lia. }
        eapply IH.
        * rewrite M.gso; [| intros Hc; subst; eapply Hnin; now left ].
          rewrite <- app_assoc. simpl. eassumption.
        * eassumption.
        * intros Hc; eapply Hnin; now right.
        * lia.
        * intros rho2' Hs. eapply Hk. eapply set_lists_cons_permut; eauto.
  Qed.

  Lemma E_projs_r (V : nat -> val -> val -> Prop) P ex k p1 w c g vs zs e2 rho2
        (Hpt : post_target_steps P) :
    M.get g rho2 = Some (Vconstr w c vs) ->
    NoDup zs -> ~ List.In g zs -> length zs = length vs ->
    (forall rho2', set_lists zs vs rho2 = Some rho2' -> E' cenv V P ex k p1 (e2, rho2')) ->
    E' cenv V P ex k p1 (projs zs w c 0 g e2, rho2).
  Proof.
    intros. eapply (E_projs_r_gen V P ex k p1 w c g e2 Hpt zs [] vs); eauto.
  Qed.

  (** ** Records of a bundle *)

  Fixpoint bundle_internal (B : fundefs) : Prop :=
    match B with
    | Fcons _ w _ _ B => exposedb w = false /\ bundle_internal B
    | Fnil => True
    end.

  Inductive recs_env (vs : list val) : fundefs -> list ctor_tag -> env -> env -> Prop :=
  | RE_nil : forall rho, recs_env vs Fnil [] rho rho
  | RE_cons : forall f w xs e B c cs rho rho',
      recs_env vs B cs (M.set f (Vconstr w c vs) rho) rho' ->
      recs_env vs (Fcons f w xs e B) (c :: cs) rho rho'.

  Fixpoint same_length (B : fundefs) (cs : list ctor_tag) : Prop :=
    match B, cs with
    | Fcons _ _ _ _ B, _ :: cs => same_length B cs
    | Fnil, [] => True
    | _, _ => False
    end.

  Lemma E_bind_records_r (V : nat -> val -> val -> Prop) P ex k p1 fvs vs e2
        (Hpt : post_target_steps P) :
    forall B cs rho2,
      get_list fvs rho2 = Some vs ->
      Disjoint _ (FromList fvs) (name_in_fundefs B) ->
      same_length B cs ->
      bundle_internal B ->
      (forall rho2', recs_env vs B cs rho2 rho2' -> E' cenv V P ex k p1 (e2, rho2')) ->
      E' cenv V P ex k p1 (bind_records B cs fvs e2, rho2).
  Proof.
    induction B as [f w xs e B IH |]; intros cs rho2 Hget Hdis Hlen Hint Hk.
    - destruct cs as [| c cs]; simpl in Hlen; try contradiction. destruct Hint as [Hw Hint].
      simpl. eapply E_target_step; [ eassumption | |].
      + intros. eapply wrap_constr; eauto. congruence.
      + eapply IH; eauto.
        * rewrite get_list_set_neq; eauto. intros Hc. eapply Hdis. constructor; eauto. now left.
        * eapply Disjoint_Included_r; [| eassumption ]. simpl. sets.
        * intros rho2' Hr. eapply Hk. constructor; eauto.
    - destruct cs; simpl in Hlen; try contradiction. simpl. eapply Hk. constructor.
  Qed.

  Lemma recs_env_get_neq vs B cs rho rho' x :
    recs_env vs B cs rho rho' -> ~ name_in_fundefs B x -> M.get x rho' = M.get x rho.
  Proof.
    intros H. induction H; intros Hn; eauto.
    rewrite IHrecs_env. rewrite M.gso; eauto.
    intros Hc; subst; eapply Hn; left; constructor.
    intros Hc; eapply Hn; now right.
  Qed.

  Lemma name_in_fnames B x : name_in_fundefs B x -> List.In x (fnames B).
  Proof. induction B; simpl; intros H; inv H; [ inv H0; now left | right; eauto ]. Qed.

  Lemma recs_env_get_eq vs B cs rho rho' h w c :
    recs_env vs B cs rho rho' -> NoDup (fnames B) -> rec_of B cs h = Some (w, c) ->
    M.get h rho' = Some (Vconstr w c vs).
  Proof.
    intros H. induction H; intros Hnd Hr; simpl in *; try congruence. inv Hnd.
    destruct (M.elt_eq h f); subst.
    - inv Hr. erewrite recs_env_get_neq; eauto. rewrite M.gss. reflexivity.
      intros Hc. eapply H2. eapply name_in_fnames; eauto.
    - eauto.
  Qed.

  Lemma bstep_bind_records ex vs fvs e' cin r cout :
    forall B cs rho rho',
      recs_env vs B cs rho rho' ->
      get_list fvs rho = Some vs ->
      Disjoint _ (FromList fvs) (name_in_fundefs B) ->
      bundle_internal B ->
      bstep_fuel cenv ex rho' e' cin r cout ->
      exists cin' cout', bstep_fuel cenv ex rho (bind_records B cs fvs e') cin' r cout' /\
                         (B = Fnil \/ ge cin' (cin <+> one_w (Efun Fnil e'))) /\ ge cin' cin.
  Proof.
    intros B cs rho rho' H. induction H; intros Hget Hdis Hint Hs.
    - do 2 eexists. split; [ eassumption | split; [ now left | eapply ge_refl ] ].
    - destruct Hint as [Hw Hint]. simpl.
      edestruct IHrecs_env as (cin1 & cout1 & Hs1 & _ & Hge1); eauto.
      + rewrite get_list_set_neq; eauto. intros Hc. eapply Hdis. constructor; eauto. now left.
      + eapply Disjoint_Included_r; [| eassumption ]. simpl. sets.
      + do 2 eexists. split; [| split ].
        * econstructor 2; [ econstructor; eauto; congruence |]. eapply bstep_fuel_ex_exposed; eauto.
        * right. rewrite (one_w_eq (Econstr _ _ _ _ _) (Efun Fnil e')). eapply ge_add; eauto. eapply ge_refl.
        * eapply ge_trans; [ eapply ge_plus_r | eassumption ].
  Qed.

End Defunc.

(** * Specification *)

Section Spec.

  Variable (L : M.t (list ctor_tag)).     (* lambda sets of internal webs *)
  Variable (T : M.t (var * web * nat)).   (* tag -> code function, its web, number of fields *)
  Variable (Btop : fundefs).              (* the lifted code functions *)

  Definition Code : Ensemble var := name_in_fundefs Btop.

  Definition alts_ok (w : web) (alts : list alt) (avoid : Ensemble var) : Prop :=
    L ! w = Some (map alt_tag alts) /\
    Forall (fun a => let '(c, code, wc, zs) := a in
                     T ! c = Some (code, wc, length zs) /\ NoDup zs /\
                     Disjoint _ (FromList zs) (avoid :|: Code)) alts.

  Inductive trans : exp -> exp -> Prop :=
  | Trans_constr :
      forall x w t ys e e',
        ~ Code x -> trans e e' ->
        trans (Econstr x w t ys e) (Econstr x w t ys e')
  | Trans_proj :
      forall x w t n y e e',
        ~ Code x -> trans e e' ->
        trans (Eproj x w t n y e) (Eproj x w t n y e')
  | Trans_case_nil :
      forall x w, trans (Ecase x w []) (Ecase x w [])
  | Trans_case_cons :
      forall x w c e e' cl cl',
        trans e e' -> trans (Ecase x w cl) (Ecase x w cl') ->
        trans (Ecase x w ((c, e) :: cl)) (Ecase x w ((c, e') :: cl'))
  | Trans_letapp_exposed :
      forall x f w ys e e',
        exposedb w = true -> ~ Code x -> trans e e' ->
        trans (Eletapp x f w ys e) (Eletapp x f w ys e')
  | Trans_letapp :
      forall x f w ys e e' alts,
        exposedb w = false -> ~ Code x ->
        alts_ok w alts (f |: FromList ys :|: occurs_free e) ->
        trans e e' ->
        trans (Eletapp x f w ys e)
              (dispatch f w alts (fun code wc zs => Eletapp x code wc (zs ++ ys) e'))
  | Trans_app_exposed :
      forall f w ys, exposedb w = true -> trans (Eapp f w ys) (Eapp f w ys)
  | Trans_app :
      forall f w ys alts,
        exposedb w = false ->
        alts_ok w alts (f |: FromList ys) ->
        trans (Eapp f w ys) (dispatch f w alts (fun code wc zs => Eapp code wc (zs ++ ys)))
  | Trans_fun_exposed :
      forall B B' e e',
        trans_fundefs B B' -> Disjoint _ (name_in_fundefs B) Code -> trans e e' ->
        trans (Efun B e) (Efun B' e')
  | Trans_fun :
      forall B cs fvs e e',
        B <> Fnil ->
        trans_bundle B cs fvs B cs ->
        NoDup (fnames B) ->
        Disjoint _ (FromList fvs) (name_in_fundefs B :|: Code) ->
        Disjoint _ (name_in_fundefs B) Code ->
        FromList fvs \subset occurs_free (Efun B e) ->
        trans e e' ->
        trans (Efun B e) (bind_records B cs fvs e')
  | Trans_prim_val : forall x p e, trans (Eprim_val x p e) (Eprim_val x p e)
  | Trans_prim : forall x p ys e, trans (Eprim x p ys e) (Eprim x p ys e)
  | Trans_halt : forall x, trans (Ehalt x) (Ehalt x)
  (* exposed bundles: functions keep their calling convention *)
  with trans_fundefs : fundefs -> fundefs -> Prop :=
  | Trans_Fnil : trans_fundefs Fnil Fnil
  | Trans_Fcons :
      forall f w xs e e' B B',
        exposedb w = true -> Disjoint _ (FromList xs) Code ->
        trans e e' -> trans_fundefs B B' ->
        trans_fundefs (Fcons f w xs e B) (Fcons f w xs e' B')
  (* internal bundles: [trans_bundle B0 cs0 fvs B cs] checks the code of the
     functions [B] (a suffix of [B0], with tags [cs]) *)
  with trans_bundle : fundefs -> list ctor_tag -> list var -> fundefs -> list ctor_tag -> Prop :=
  | TB_nil : forall B0 cs0 fvs, trans_bundle B0 cs0 fvs Fnil []
  | TB_cons :
      forall B0 cs0 fvs f w xs e B c cs lams code wc e',
        exposedb w = false -> L ! w = Some lams -> List.In c lams ->
        T ! c = Some (code, wc, length fvs) -> exposedb wc = false ->
        find_def code Btop = Some (wc, fvs ++ xs, bind_records B0 cs0 fvs e') ->
        trans e e' ->
        NoDup (fvs ++ xs) ->
        Disjoint _ (FromList xs) (name_in_fundefs B0 :|: Code) ->
        occurs_free e \subset FromList xs :|: (name_in_fundefs B0 :|: FromList fvs) ->
        trans_bundle B0 cs0 fvs B cs ->
        trans_bundle B0 cs0 fvs (Fcons f w xs e B) (c :: cs).

  (** The whole program: the code functions are bound at the top. *)
  Definition trans_top (e : exp) (e_t : exp) : Prop :=
    exists e', e_t = Efun Btop e' /\ trans e e' /\ Disjoint _ (occurs_free e) Code.

  (** ** Syntactic facts *)

  Lemma trans_bundle_same_length B0 cs0 fvs B cs :
    trans_bundle B0 cs0 fvs B cs -> same_length B cs.
  Proof. intros H; induction H; simpl; eauto. Qed.

  Lemma trans_bundle_internal B0 cs0 fvs B cs :
    trans_bundle B0 cs0 fvs B cs -> bundle_internal B.
  Proof. intros H; induction H; simpl; eauto. Qed.

  Lemma trans_bundle_lookup B0 cs0 fvs B cs f w c :
    trans_bundle B0 cs0 fvs B cs ->
    rec_of B cs f = Some (w, c) ->
    exists xs e lams code wc e',
      find_def f B = Some (w, xs, e) /\ exposedb w = false /\
      L ! w = Some lams /\ List.In c lams /\
      T ! c = Some (code, wc, length fvs) /\ exposedb wc = false /\
      find_def code Btop = Some (wc, fvs ++ xs, bind_records B0 cs0 fvs e') /\
      trans e e' /\ NoDup (fvs ++ xs) /\
      Disjoint _ (FromList xs) (name_in_fundefs B0 :|: Code) /\
      occurs_free e \subset FromList xs :|: (name_in_fundefs B0 :|: FromList fvs).
  Proof.
    intros H. induction H; simpl; intros Hr; try congruence.
    destruct (M.elt_eq f f0); subst.
    - inv Hr. do 6 eexists. split; [ reflexivity |]. repeat (split; [ eassumption |]). eassumption.
    - eauto.
  Qed.

  Lemma rec_of_names B cs f :
    same_length B cs -> name_in_fundefs B f -> exists w c, rec_of B cs f = Some (w, c).
  Proof.
    revert cs; induction B; intros cs Hl Hn; destruct cs; simpl in *; try contradiction.
    destruct (M.elt_eq f v); eauto. inv Hn; [ inv H; congruence | eauto ].
  Qed.

  Lemma rec_of_find_def B cs f w c :
    rec_of B cs f = Some (w, c) -> exists xs e, find_def f B = Some (w, xs, e).
  Proof.
    revert cs; induction B; intros cs Hr; destruct cs; simpl in *; try congruence.
    destruct (M.elt_eq f v); [ inv Hr |]; eauto.
  Qed.

  Lemma trans_fundefs_names B B' :
    trans_fundefs B B' -> forall f, name_in_fundefs B f <-> name_in_fundefs B' f.
  Proof.
    intros H; induction H; intros g; simpl; try reflexivity;
      split; intros Hin;
      (destruct Hin as [g' Hg | g' Hg]; [ now left | right; now apply IHtrans_fundefs ]).
  Qed.

  Lemma trans_fundefs_find_def B B' f w xs e :
    trans_fundefs B B' -> find_def f B = Some (w, xs, e) ->
    exists e', find_def f B' = Some (w, xs, e') /\ trans e e' /\ exposedb w = true /\
               Disjoint _ (FromList xs) Code.
  Proof.
    intros H; induction H; simpl; intros Hfin; try congruence.
    destruct (M.elt_eq f f0); subst; eauto. inv Hfin. eauto.
  Qed.

  Lemma trans_case_tags x w cl cl' :
    trans (Ecase x w cl) (Ecase x w cl') -> Forall2 (fun p p' => fst p = fst p') cl cl'.
  Proof.
    revert cl'. induction cl as [| [c e] cl IH]; intros cl' H; inv H; constructor; eauto.
  Qed.

  Lemma find_alt (g : var) (w : web) (alts : list alt) call c :
    List.In c (map alt_tag alts) ->
    exists code wc zs n,
      List.In (c, code, wc, zs) alts /\
      find_tag_nth (map (fun '(c, code, wc, zs) => (c, projs zs w c 0 g (call code wc zs))) alts)
                   c (projs zs w c 0 g (call code wc zs)) n.
  Proof.
    induction alts as [| [[[c' code] wc] zs] alts IH]; simpl; intros Hin; [ contradiction |].
    destruct (M.elt_eq c' c); subst.
    - do 4 eexists. split; [ now left | constructor ].
    - destruct Hin as [Heq | Hin]; [ congruence |].
      edestruct IH as (code'' & wc'' & zs'' & n' & Hin' & Hft); eauto.
      do 4 eexists. split; [ now right; eauto | econstructor; eauto ].
  Qed.

End Spec.

(** * The logical relation *)

Section DefuncRel.

  Variable (cenv : term.ctor_env).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Local Notation PostT := (@exposed.PostT fuel trace).
  Local Notation PostGT := (@exposed.PostGT fuel trace).
  Local Notation VTransT := (@exposed.VTransT fuel trace).

  Variables (L : M.t (list ctor_tag)) (T : M.t (var * web * nat)) (Btop : fundefs).

  Local Notation Code := (Code Btop).
  Local Notation trans := (trans L T Btop).

  (** Code functions are defined at the top *)
  Hypothesis HT : forall c code wc n, T ! c = Some (code, wc, n) -> Code code.
  (** The tags of a lambda set belong to the same inductive type *)
  Hypothesis HL :
    forall w lams, L ! w = Some lams ->
                   exists it, Forall (fun c => exists info, M.get c cenv = Some info /\
                                                            term.ctor_ind_tag info = it) lams.

  (** Internal closures are related to their records: calling the closure
      is related to calling the code selected by the tag of the record on
      the fields of the record and the arguments.  [rtop] is the environment
      of the code functions (the environment of the whole program). *)
  Definition VT_dfn (rtop : env) : VTransT :=
    fun PG V' k v1 v2 =>
      match v1, v2 with
      | Vfun rho1 B1 f1, Vconstr w c vs2 =>
          fun_web B1 f1 = Some w /\
          exists lams code wc,
            L ! w = Some lams /\ List.In c lams /\
            T ! c = Some (code, wc, length vs2) /\ exposedb wc = false /\
            forall vs1 args2 j xs1 e1 rho1',
              length vs1 = length args2 ->
              find_def f1 B1 = Some (w, xs1, e1) ->
              Some rho1' = set_lists xs1 vs1 (def_funs B1 B1 rho1 rho1) ->
              exists xs2 e2 rho2',
                find_def code Btop = Some (wc, xs2, e2) /\
                Some rho2' = set_lists xs2 (vs2 ++ args2) (def_funs Btop Btop rtop rtop) /\
                (j < k -> Forall2 (V' j) vs1 args2 -> E' cenv V' PG false j (e1, rho1') (e2, rho2'))
      | _, _ => False
      end.

  Lemma VT_dfn_eq rtop PG V' k rho1 B1 f1 w c vs2 :
    VT_dfn rtop PG V' k (Vfun rho1 B1 f1) (Vconstr w c vs2) =
    (fun_web B1 f1 = Some w /\
     exists lams code wc,
       L ! w = Some lams /\ List.In c lams /\
       T ! c = Some (code, wc, length vs2) /\ exposedb wc = false /\
       forall vs1 args2 j xs1 e1 rho1',
         length vs1 = length args2 ->
         find_def f1 B1 = Some (w, xs1, e1) ->
         Some rho1' = set_lists xs1 vs1 (def_funs B1 B1 rho1 rho1) ->
         exists xs2 e2 rho2',
           find_def code Btop = Some (wc, xs2, e2) /\
           Some rho2' = set_lists xs2 (vs2 ++ args2) (def_funs Btop Btop rtop rtop) /\
           (j < k -> Forall2 (V' j) vs1 args2 -> E' cenv V' PG false j (e1, rho1') (e2, rho2'))).
  Proof. reflexivity. Qed.

  Global Instance VTransProps_dfn rtop : VTransProps (VT_dfn rtop).
  Proof.
    constructor; unfold VT_dfn.
    - intros PG V1 V2 k v1 v2 Hext. destruct v1, v2; try easy.
      intros (Hw & lams & code & wc & HL' & Hin & HTc & Hwc & Hb).
      split; [ eassumption |]. exists lams, code, wc. do 4 (split; [ eassumption |]).
      intros vs1 args2 j xs1 e1 rho1' Hlen Hf1 Hs1.
      edestruct (Hb vs1 args2 j xs1 e1 rho1' Hlen Hf1 Hs1) as (xs2 & e2 & rho2' & Hf2 & Hs2 & Hbody).
      do 3 eexists. split; [ eassumption | split; [ eassumption |] ].
      intros Hlt Hall. eapply E'_ext; [| eapply Hbody; eauto ].
      + intros. eapply Hext. lia.
      + eapply Forall2_monotonic; [| eassumption ]. intros. eapply Hext; eauto.
    - intros PG V k j v1 v2 Hmono. destruct v1, v2; try easy.
      intros (Hw & lams & code & wc & HL' & Hin & HTc & Hwc & Hb) Hleq.
      split; [ eassumption |]. exists lams, code, wc. do 4 (split; [ eassumption |]).
      intros vs1 args2 i xs1 e1 rho1' Hlen Hf1 Hs1.
      edestruct (Hb vs1 args2 i xs1 e1 rho1' Hlen Hf1 Hs1) as (xs2 & e2 & rho2' & Hf2 & Hs2 & Hbody).
      do 3 eexists. split; [ eassumption | split; [ eassumption |] ].
      intros Hlt. eapply Hbody. lia.
  Qed.

  Lemma caseConsistent_lams lams c (cl : list (ctor_tag * term.exp)) :
    (exists it, Forall (fun c => exists info, M.get c cenv = Some info /\ term.ctor_ind_tag info = it) lams) ->
    List.In c lams -> Forall (fun p => List.In (fst p) lams) cl ->
    term_util.caseConsistent cenv cl c.
  Proof.
    intros [it Hall] Hc Hcl. eapply Forall_forall in Hc; [| eassumption ].
    destruct Hc as (info & Hget & Hit).
    induction Hcl; [ constructor |]. destruct x as [c' e'].
    eapply Forall_forall in H; [| eassumption ]. destruct H as (info' & Hget' & Hit').
    econstructor; eauto. congruence.
  Qed.

  Lemma dispatch_cc w alts g call c :
    L ! w = Some (map alt_tag alts) -> List.In c (map alt_tag alts) ->
    term_util.caseConsistent cenv
      (erase_branches (map (fun '(c, code, wc, zs) => (c, projs zs w c 0 g (call code wc zs))) alts)) c.
  Proof.
    intros HLw Hin. eapply caseConsistent_lams; eauto.
    clear. induction alts as [| [[[c code] wc] zs] alts IH]; simpl; constructor.
    - simpl. now left.
    - eapply Forall_impl; [| exact IH ]. intros p Hp. now right.
  Qed.

  Context (P PG : PostT) {Hprops : Post_properties cenv P P PG} (HptP : post_target_steps P).

  Lemma P_PG : inclusion _ P PG.
  Proof. destruct Hprops; assumption. Qed.

  Section WithTop.

    Context (rtop : env) (Hrtop : wf_env rtop).

    Local Notation VT := (VT_dfn rtop).
    Local Notation V := (V cenv VT PG).
    Local Notation E := (E cenv VT PG).
    Local Notation G := (G cenv VT PG).

    Definition code_env (rho : env) := forall c, Code c -> M.get c rho = Some (Vfun rtop Btop c).

    Definition Gd k S rho1 rho2 :=
      G k S rho1 rho2 /\ term_util.binding_in_map S rho1 /\ code_env rho2.

    Definition IH_exp k :=
      forall m ex e e' rho1 rho2,
        m < k -> trans e e' -> Gd m (occurs_free e) rho1 rho2 -> E P ex m (e, rho1) (e', rho2).

    (** ** Environment lemmas *)

    Lemma Gd_mono k j S rho1 rho2 : Gd k S rho1 rho2 -> j <= k -> Gd j S rho1 rho2.
    Proof. intros (HG & Hb & Hc) Hle. split; [ eapply (G_mono cenv VT); eauto | eauto ]. Qed.

    Lemma Gd_antimon k S1 S2 rho1 rho2 : Gd k S2 rho1 rho2 -> S1 \subset S2 -> Gd k S1 rho1 rho2.
    Proof.
      intros (HG & Hb & Hc) Hs. split; [ eapply (G_antimon cenv VT); eauto | split; eauto ].
      intros x Hx; eapply Hb; eauto.
    Qed.

    Lemma Gd_set k S rho1 rho2 x v1 v2 :
      Gd k (Setminus _ S [set x]) rho1 rho2 -> V k v1 v2 -> ~ Code x ->
      Gd k S (M.set x v1 rho1) (M.set x v2 rho2).
    Proof.
      intros (HG & Hb & Hc) Hv Hx. split; [ eapply (G_set cenv VT); eauto | split ].
      - intros y Hy. destruct (peq y x); subst; [ rewrite M.gss; eauto |].
        rewrite M.gso; eauto. eapply Hb. constructor; eauto. intros Hc'; inv Hc'; eauto.
      - intros c Hcc. rewrite M.gso; eauto. intros Heq; subst; eauto.
    Qed.

    Lemma bim_set_lists_def_funs S S0 xs vs B0 B rho0 rho rho' :
      term_util.binding_in_map S0 rho ->
      S \subset FromList xs :|: (name_in_fundefs B :|: S0) ->
      set_lists xs vs (def_funs B0 B rho0 rho) = Some rho' ->
      term_util.binding_in_map S rho'.
    Proof.
      intros Hb Hs Hset x Hx.
      destruct (in_dec peq x xs) as [Hin | Hnin].
      - eapply get_set_lists_In_xs; eauto.
      - rewrite <- (set_lists_not_In xs vs _ rho' x Hset Hnin).
        destruct (name_in_fundefs_dec B x) as [Hn | Hn].
        + rewrite def_funs_eq; eauto.
        + rewrite def_funs_neq; eauto. eapply Hb.
          eapply Hs in Hx. inv Hx; [ contradiction |]. inv H; [ contradiction | eauto ].
    Qed.

    Lemma code_env_set_lists_def_funs xs vs B0 B rho0 rho rho' :
      code_env rho ->
      Disjoint _ (FromList xs) Code -> Disjoint _ (name_in_fundefs B) Code ->
      set_lists xs vs (def_funs B0 B rho0 rho) = Some rho' ->
      code_env rho'.
    Proof.
      intros Hc Hd1 Hd2 Hset c Hcc. rewrite <- (set_lists_not_In xs vs _ rho' c Hset).
      - rewrite def_funs_neq; eauto. intros Hn; eapply Hd2; constructor; eauto.
      - intros Hin; eapply Hd1; constructor; eauto.
    Qed.

    Lemma set_lists_Forall2_get {A B} (R : A -> B -> Prop) xs vs1 vs2 rho1 rho2 rho1' rho2' x :
      set_lists xs vs1 rho1 = Some rho1' -> set_lists xs vs2 rho2 = Some rho2' ->
      Forall2 R vs1 vs2 -> List.In x xs ->
      exists v1 v2, M.get x rho1' = Some v1 /\ M.get x rho2' = Some v2 /\ R v1 v2.
    Proof.
      revert vs1 vs2 rho1' rho2'.
      induction xs as [| y xs IH]; intros vs1 vs2 rho1' rho2' Hs1 Hs2 Hall Hin; [ inv Hin |].
      destruct vs1, vs2; simpl in *; try congruence; inv Hall.
      destruct (set_lists xs vs1 rho1) eqn:Hsl1; try congruence.
      destruct (set_lists xs vs2 rho2) eqn:Hsl2; try congruence. inv Hs1; inv Hs2.
      destruct (peq x y); subst.
      - rewrite !M.gss. eauto.
      - rewrite !M.gso; eauto. destruct Hin; [ congruence | eauto ].
    Qed.

    Lemma set_lists_get_list_get {A} fvs (vs : list A) rhod rho rho' x :
      get_list fvs rhod = Some vs -> NoDup fvs ->
      set_lists fvs vs rho = Some rho' -> List.In x fvs ->
      M.get x rho' = M.get x rhod.
    Proof.
      revert vs rho'. induction fvs as [| y fvs IH]; intros vs rho' Hget Hnd Hs Hin; [ inv Hin |].
      simpl in Hget. destruct (M.get y rhod) eqn:Hy; try congruence.
      destruct (get_list fvs rhod) eqn:Hfvs; try congruence. inv Hget. inv Hnd.
      simpl in Hs. destruct (set_lists fvs l rho) eqn:Hs'; try congruence. inv Hs.
      destruct (peq x y); subst.
      - rewrite M.gss; eauto.
      - rewrite M.gso; eauto. destruct Hin; [ congruence | eauto ].
    Qed.

    Lemma recs_env_wf vs B cs rho rho' :
      recs_env vs B cs rho rho' -> wf_env rho -> Forall wf_val vs -> bundle_internal B -> wf_env rho'.
    Proof.
      intros H. induction H; intros Hwf Hvs Hint; eauto. destruct Hint.
      eapply IHrecs_env; eauto. eapply wf_env_set; eauto. constructor; eauto. congruence.
    Qed.

    Lemma recs_env_exists vs B cs rho :
      same_length B cs -> exists rho', recs_env vs B cs rho rho'.
    Proof.
      revert cs rho; induction B; intros cs rho Hl; destruct cs; simpl in Hl; try contradiction.
      - edestruct IHB as [rho' Hr]; eauto. eexists. econstructor; eauto.
      - eexists; constructor.
    Qed.

    Lemma not_exposed_internal_fun rho B f w :
      fun_web B f = Some w -> exposedb w = false -> ~ exposed_val (Vfun rho B f).
    Proof.
      intros Hfw Hw Hexp. rewrite exposed_val_Vfun in Hexp. destruct Hexp as (w' & xs & e & Hfd & Hw').
      unfold fun_web in Hfw. rewrite Hfd in Hfw. inv Hfw. congruence.
    Qed.

    Lemma not_exposed_record w c vs : exposedb w = false -> ~ exposed_val (Vconstr w c vs).
    Proof. intros Hw Hexp. rewrite exposed_val_Vconstr in Hexp. destruct Hexp. congruence. Qed.

    (** ** Records of internal bundles (Löb induction) *)

    Lemma NoDup_app_disj {A} (l1 l2 : list A) x : NoDup (l1 ++ l2) -> List.In x l2 -> ~ List.In x l1.
    Proof.
      induction l1; simpl; intros Hnd Hin Hc; [ contradiction |]. inv Hnd.
      destruct Hc as [Heq | Hc]; [ subst; apply H1; apply in_or_app; now right | eapply IHl1; eauto ].
    Qed.

    Lemma NoDup_app_l {A} (l1 l2 : list A) : NoDup (l1 ++ l2) -> NoDup l1.
    Proof.
      induction l1; simpl; intros Hnd; constructor; inv Hnd; eauto.
      intros Hc; apply H1; apply in_or_app; now left.
    Qed.

    Lemma Vrec_dfn k rho1 rhod B cs fvs vs2 :
      trans_bundle L T Btop B cs fvs B cs ->
      NoDup (fnames B) ->
      Disjoint _ (FromList fvs) (name_in_fundefs B :|: Code) ->
      Disjoint _ (name_in_fundefs B) Code ->
      IH_exp k ->
      wf_env rho1 ->
      G k (FromList fvs) rho1 rhod ->
      term_util.binding_in_map (FromList fvs) rho1 ->
      get_list fvs rhod = Some vs2 ->
      forall f w c, rec_of B cs f = Some (w, c) -> V k (Vfun rho1 B f) (Vconstr w c vs2).
    Proof.
      intros HB Hnd Hdfv Hdn. induction k as [k IHk] using lt_wf_rec.
      intros Hexp Hwf1 HG Hbind Hvs2 f w c Hr.
      pose proof (trans_bundle_same_length _ _ _ _ _ _ _ _ HB) as Hsl.
      pose proof (trans_bundle_internal _ _ _ _ _ _ _ _ HB) as Hint.
      edestruct trans_bundle_lookup as
        (xs & e & lams & code & wc & e' & Hfind & Hw & HLw & Hin & HTc & Hwc & Hcode & Htr & Hnd' & Hdxs & Hfv);
        eauto.
      assert (Hwfvs : Forall wf_val vs2) by (eapply wf_env_get_list; [ apply HG | eassumption ]).
      assert (Hlen2 : length fvs = length vs2) by (eapply get_list_length_eq; eauto).
      eapply (V_Vfun_internal cenv VT); eauto.
      - constructor; eauto. congruence.
      - eapply (not_exposed_internal_fun _ _ _ w); [ unfold fun_web; rewrite Hfind; reflexivity | eassumption ].
      - eapply not_exposed_record; eassumption.
      - rewrite VT_dfn_eq. split; [ unfold fun_web; rewrite Hfind; reflexivity |].
        exists lams, code, wc. split; [ eassumption | split; [ eassumption |] ].
        split; [ rewrite <- Hlen2; eassumption | split; [ eassumption |] ].
        intros vs1 args2 j xs1 e1 rho1' Hlen Hf1 Hs1.
        rewrite Hfind in Hf1. inv Hf1. symmetry in Hs1.
        edestruct (set_lists_length3 (def_funs Btop Btop rtop rtop) (fvs ++ xs1) (vs2 ++ args2))
          as [rho2' Hs2].
        { rewrite !length_app, Hlen2, <- Hlen. f_equal. eapply set_lists_length_eq; eauto. }
        do 3 eexists. split; [ eassumption | split; [ symmetry; eassumption |] ].
        intros Hlt Hvs.
        eapply (E_post_mono cenv VT); [ exact P_PG |].
        edestruct (set_lists_app fvs xs1 vs2 args2) as (rhox & Hsx & Hsf); eauto.
        eapply E_bind_records_r; eauto.
        + eapply get_list_set_lists; [ eapply NoDup_app_l; eassumption | eassumption ].
        + eapply Disjoint_Included_r; [| eassumption ]. sets.
        + intros rho2'' Hrecs. eapply Hexp; eauto.
          assert (Hwf1' : wf_env rho1').
          { eapply (wf_env_set_lists (def_funs B B rho1 rho1) rho1' xs1 vs1); [ eapply wf_env_def_funs; eauto | | exact Hs1 ].
            eapply (Forall2_V_wf_l cenv VT); eauto. }
          assert (Hwf2' : wf_env rho2').
          { eapply (wf_env_set_lists (def_funs Btop Btop rtop rtop) rho2' (fvs ++ xs1) (vs2 ++ args2));
              [ eapply wf_env_def_funs; eauto | | exact Hs2 ].
            eapply Forall_app; split; eauto. eapply (Forall2_V_wf_r cenv VT); eauto. }
          split; [ split; [| split ] | split ].
          * eassumption.
          * eapply recs_env_wf; eauto.
          * intros x Hx v1 Hget1. eapply Hfv in Hx.
            destruct (name_in_fundefs_dec B x) as [Hn | Hn].
            -- (* a sibling: closure vs record *)
               edestruct (rec_of_names B cs x) as (w' & c' & Hr'); eauto.
               rewrite <- (set_lists_not_In xs1 vs1 _ rho1' x Hs1) in Hget1;
                 [| intros Hc; eapply Hdxs; constructor; [ eassumption | now left ] ].
               rewrite def_funs_eq in Hget1; eauto. inv Hget1.
               eexists. erewrite recs_env_get_eq; eauto. split; [ reflexivity |].
               eapply IHk; eauto.
               ++ intros m ex' e3 e3' r1 r2 Hm. eapply Hexp. lia.
               ++ eapply (G_mono cenv VT); eauto. lia.
            -- erewrite recs_env_get_neq; eauto.
               destruct (in_dec peq x xs1) as [Hxs | Hxs].
               ++ (* a parameter *)
                  edestruct (set_lists_Forall2_get (V j) xs1 vs1 args2) as (v1' & v2' & Hg1 & Hg2 & Hr12);
                    [ eassumption | eassumption | eassumption | eassumption |].
                  rewrite Hg1 in Hget1. inv Hget1. eexists. split; eauto.
                  erewrite <- set_lists_not_In; [ eassumption | eassumption |].
                  intros Hc. eapply NoDup_app_disj; eauto.
               ++ (* a field *)
                  inv Hx; [ contradiction |]. inv H; [ contradiction |].
                  rewrite <- (set_lists_not_In xs1 vs1 _ rho1' x Hs1 Hxs) in Hget1.
                  rewrite def_funs_neq in Hget1; eauto.
                  rewrite (set_lists_get_list_get fvs vs2 rhod rhox rho2' x Hvs2 (NoDup_app_l _ _ Hnd') Hsf
                                                  ltac:(eassumption)).
                  edestruct (G_var_rel cenv VT PG k _ rho1 rhod x HG ltac:(eassumption) v1 Hget1)
                    as (v2 & Hg2 & Hv).
                  eexists; split; [ eassumption |]. eapply (V_mono cenv VT); [ eassumption | lia ].
          * eapply bim_set_lists_def_funs; eauto.
          * intros c' Hc'.
            rewrite (recs_env_get_neq _ _ _ _ _ c' Hrecs); [| intros Hn; eapply Hdn; constructor; eauto ].
            rewrite <- (set_lists_not_In (fvs ++ xs1) (vs2 ++ args2) _ rho2' c' Hs2).
            -- rewrite def_funs_eq; [ reflexivity | exact Hc' ].
            -- intros Hin2. apply in_app_or in Hin2. destruct Hin2 as [Hin2 | Hin2].
               ++ eapply Hdfv. constructor; [ exact Hin2 | now right ].
               ++ eapply Hdxs. constructor; [ exact Hin2 | now right ].
    Qed.

    Lemma Vexp_dfn k rho1 rho2 B B' :
      trans_fundefs L T Btop B B' ->
      Disjoint _ (name_in_fundefs B) Code ->
      IH_exp k ->
      Gd k (occurs_free_fundefs B) rho1 rho2 ->
      forall f, name_in_fundefs B f -> V k (Vfun rho1 B f) (Vfun rho2 B' f).
    Proof.
      intros HB Hdn. induction k as [k IHk] using lt_wf_rec. intros Hexp Hgd f Hin.
      pose proof Hgd as (HG & Hbind & Hcode).
      edestruct name_in_fundefs_find_def as (w & xs & e & Hfind); eauto.
      edestruct trans_fundefs_find_def as (e' & Hfind' & Htr & Hw & Hdxs); eauto.
      assert (Hnames : forall g, name_in_fundefs B g <-> name_in_fundefs B' g)
        by (eapply trans_fundefs_names; eauto).
      eapply (V_Vfun_exposed cenv VT); eauto; try now apply HG.
      eapply (V_fun_def cenv VT); eauto.
      intros j vs1 vs2 rho1' rho2' Hlt Hexpv Hvs Hs1 Hs2.
      eapply (E_post_mono cenv VT); [ exact P_PG |].
      eapply Hexp; eauto. split; [| split ].
      - eapply (G_antimon cenv VT); [| eapply occurs_free_in_fun; eassumption ].
        eapply (G_set_lists cenv VT); eauto.
        eapply (G_def_funs cenv VT).
        + eapply (G_antimon cenv VT). eapply (G_mono cenv VT); eauto. lia. eapply fun_body_scope_subset.
        + apply HG.
        + apply HG.
        + eassumption.
        + intros g Hg. eapply IHk; eauto.
          * intros m ex e1 e2 r1 r2 Hm. eapply Hexp. lia.
          * eapply Gd_mono; eauto. lia.
      - eapply bim_set_lists_def_funs; [ eassumption | eapply occurs_free_in_fun; eassumption | eassumption ].
      - eapply code_env_set_lists_def_funs; [ eassumption | eassumption | | eassumption ].
        constructor. intros z Hz. inv Hz. eapply Hdn. constructor; [ apply (proj2 (Hnames z)); eassumption | eassumption ].
    Qed.

    Lemma E_fun_int ex k rho1 rho2 B cs fvs e e' :
      B <> Fnil ->
      trans_bundle L T Btop B cs fvs B cs ->
      NoDup (fnames B) ->
      Disjoint _ (FromList fvs) (name_in_fundefs B :|: Code) ->
      Disjoint _ (name_in_fundefs B) Code ->
      FromList fvs \subset occurs_free (Efun B e) ->
      IH_exp k ->
      (forall rho1' rho2', Gd k (occurs_free e) rho1' rho2' -> E P ex k (e, rho1') (e', rho2')) ->
      Gd k (occurs_free (Efun B e)) rho1 rho2 ->
      E P ex k (Efun B e, rho1) (bind_records B cs fvs e', rho2).
    Proof.
      intros Hne HB Hnd Hdfv Hdn Hfvs Hexp Hcont Hgd.
      pose proof Hgd as (HG & Hbind & Hcode).
      pose proof Hprops as [Hcon Hproj Hfun Hchd Hctl Happ Hlet HletO HOOT Hbase HGP].
      pose proof (trans_bundle_same_length _ _ _ _ _ _ _ _ HB) as Hsl.
      pose proof (trans_bundle_internal _ _ _ _ _ _ _ _ HB) as Hint.
      edestruct (term_util.binding_in_map_get_list (occurs_free (Efun B e)) rho1 fvs) as [vs1 Hg1];
        [ eassumption | eassumption |].
      edestruct (G_get_list cenv VT PG k _ rho1 rho2 fvs vs1 HG Hfvs Hg1) as (vs2 & Hg2 & Hvs).
      edestruct (recs_env_exists vs2 B cs rho2 Hsl) as [rho2' Hrecs].
      assert (Hwfvs : Forall wf_val vs2) by (eapply wf_env_get_list; [ apply HG | eassumption ]).
      assert (Hgd' : Gd k (occurs_free e) (def_funs B B rho1 rho1) rho2').
      { split; [ split; [| split ] | split ].
        - eapply wf_env_def_funs; apply HG.
        - eapply recs_env_wf; eauto. apply HG.
        - intros x Hx v1 Hget1.
          destruct (name_in_fundefs_dec B x) as [Hn | Hn].
          + rewrite def_funs_eq in Hget1; eauto. inv Hget1.
            edestruct (rec_of_names B cs x) as (w & c & Hr); eauto.
            eexists. erewrite recs_env_get_eq; eauto. split; [ reflexivity |].
            eapply Vrec_dfn; eauto.
            * apply HG.
            * eapply (G_antimon cenv VT); eauto.
            * intros z Hz; eapply Hbind; eauto.
          + rewrite def_funs_neq in Hget1; eauto. rewrite (recs_env_get_neq _ _ _ _ _ x Hrecs Hn).
            eapply (G_var_rel cenv VT PG k _ rho1 rho2 x HG); [| eassumption ].
            eapply occurs_free_Efun. right. constructor; eauto.
        - intros x Hx. destruct (name_in_fundefs_dec B x) as [Hn | Hn].
          + rewrite def_funs_eq; eauto.
          + rewrite def_funs_neq; eauto. eapply Hbind. eapply occurs_free_Efun. right. constructor; eauto.
        - intros c Hc. rewrite (recs_env_get_neq _ _ _ _ _ c Hrecs); [ eauto |].
          intros Hn; eapply Hdn; constructor; eauto. }
      intros r1 cin cout Hleq Hs. inv Hs.
      - exists OOT, cin, <0>. split.
        + destruct B as [f w xs eb B |]; [| congruence ]. destruct cs; simpl in Hsl; [ contradiction |].
          simpl. constructor. eapply lt_one_w; eassumption.
        + split; [ eapply HOOT; eassumption | exact I ].
      - inv H.
        edestruct (Hcont _ _ Hgd') as (r2 & cin' & cout' & Hs2 & Hpost & HR); [| eassumption |].
        { rewrite to_nat_add in Hleq. lia. }
        edestruct (bstep_bind_records cenv ex vs2 fvs e' cin' r2 cout' B cs rho2 rho2')
          as (cin'' & cout'' & Hs3 & [ Hnil | Hge ] & _); eauto.
        + eapply Disjoint_Included_r; [| eassumption ]. sets.
        + congruence.
        + exists r2, cin'', cout''. split; [ eassumption | split ].
          * eapply HptP; [| eassumption ].
            eapply (Hfun B e rho1 Fnil e' rho2'). exact Hpost.
          * eapply (R_mono cenv VT); eauto. rewrite to_nat_add. lia.
    Qed.

    Lemma Gd_set_lists_r k S rho1 rho2 rho2' zs vs :
      Gd k S rho1 rho2 -> Disjoint _ (FromList zs) (S :|: Code) -> Forall wf_val vs ->
      set_lists zs vs rho2 = Some rho2' -> Gd k S rho1 rho2'.
    Proof.
      intros (HG & Hb & Hc) Hd Hwf Hs. split; [| split; [ exact Hb |] ].
      - split; [ apply HG | split; [ eapply wf_env_set_lists; [ apply HG | eassumption | eassumption ] |] ].
        intros x Hx v1 Hget. edestruct (G_var_rel cenv VT PG k S rho1 rho2 x HG Hx v1 Hget) as (v2 & Hg2 & Hv).
        eexists; split; [| exact Hv ]. rewrite <- (set_lists_not_In zs vs _ rho2' x Hs); [ exact Hg2 |].
        intros Hin. eapply Hd. constructor; [ exact Hin | now left ].
      - intros c Hcc. rewrite <- (set_lists_not_In zs vs _ rho2' c Hs); [ eauto |].
        intros Hin. eapply Hd. constructor; [ exact Hin | now right ].
    Qed.

    (** ** Calls through internal webs *)

    Lemma dispatch_lookup k S rho1 rho2 f w ys alts call rhoc B h :
      exposedb w = false ->
      alts_ok L T Btop w alts ys ->
      Gd k S rho1 rho2 -> S f ->
      M.get f rho1 = Some (Vfun rhoc B h) -> fun_web B h = Some w ->
      exists c vs2 code wc zs n,
        M.get f rho2 = Some (Vconstr w c vs2) /\
        V k (Vfun rhoc B h) (Vconstr w c vs2) /\
        List.In (c, code, wc, zs) alts /\
        find_tag_nth (map (fun '(c, code, wc, zs) => (c, projs zs w c 0 f (call code wc zs))) alts)
                     c (projs zs w c 0 f (call code wc zs)) n /\
        term_util.caseConsistent cenv
          (erase_branches (map (fun '(c, code, wc, zs) => (c, projs zs w c 0 f (call code wc zs))) alts)) c /\
        T ! c = Some (code, wc, length vs2) /\ length zs = length vs2 /\ NoDup zs /\
        Disjoint _ (FromList zs) (ys :|: Code).
    Proof.
      intros Hw [HLw Halts] (HG & Hbind & Hcode) Hfin Hf1 Hfw.
      edestruct (G_var_rel cenv VT PG k S rho1 rho2 f HG Hfin _ Hf1) as (v2 & Hf2 & Hv).
      pose proof Hv as Hv'.
      eapply (V_internal_fun cenv VT) in Hv; [| eapply not_exposed_internal_fun; eauto ].
      destruct v2 as [w2 c vs2 | | |]; try contradiction.
      rewrite VT_dfn_eq in Hv. destruct Hv as (Hfw2 & lams & code & wc & HL2 & Hinc & HTc & Hwc & Hb).
      rewrite Hfw in Hfw2. inv Hfw2. rewrite HLw in HL2. inv HL2.
      edestruct (find_alt f w2 alts call c Hinc) as (code' & wc' & zs & n & Hina & Hft).
      eapply Forall_forall in Halts; [| exact Hina ]. destruct Halts as (HTc' & Hndz & Hdz).
      rewrite HTc in HTc'. injection HTc' as Hc1 Hc2 Hlz. subst code' wc'.
      exists c, vs2, code, wc, zs, n. repeat (split; [ eassumption |]).
      split; [ eapply dispatch_cc; eauto |].
      split; [ eassumption | split; [ congruence | split; eassumption ] ].
    Qed.

    Lemma E_app_dfn ex k rho1 rho2 f w ys alts S :
      exposedb w = false ->
      alts_ok L T Btop w alts (f |: FromList ys) ->
      Gd k S rho1 rho2 -> S f -> FromList ys \subset S ->
      E P ex k (Eapp f w ys, rho1) (dispatch f w alts (fun code wc zs => Eapp code wc (zs ++ ys)), rho2).
    Proof.
      intros Hw Halts Hgd Hfin Hys.
      pose proof Hgd as (HG & Hbind & Hcode).
      pose proof Hprops as [Hcon Hproj Hfun Hchd Hctl Happ Hlet HletO HOOT Hbase HGP].
      assert (Hstuck : (forall rhoc B h, M.get f rho1 = Some (Vfun rhoc B h) -> fun_web B h = Some w -> False) ->
                       E P ex k (Eapp f w ys, rho1)
                         (dispatch f w alts (fun code wc zs => Eapp code wc (zs ++ ys)), rho2)).
      { intros Hno r1 cin cout Hleq Hs. inv Hs.
        - exists OOT, cin, <0>. split; [ constructor; eapply lt_one_w; eassumption |].
          split; [ eapply HOOT; eassumption | exact I ].
        - inv H. exfalso. eapply Hno; [ eassumption |]. unfold fun_web.
          match goal with [ Hd : find_def _ _ = Some _ |- _ ] => rewrite Hd end. reflexivity. }
      destruct (M.get f rho1) as [[ | rhoc B h | | ] |] eqn:Hf1; try (eapply Hstuck; intros; congruence).
      destruct (fun_web B h) as [w' |] eqn:Hfw; [| eapply Hstuck; intros; congruence ].
      destruct (peq w' w); [ subst | eapply Hstuck; intros; congruence ].
      edestruct (dispatch_lookup k S rho1 rho2 f w (f |: FromList ys) alts
                   (fun code wc zs => Eapp code wc (zs ++ ys)) rhoc B h)
        as (c & vs2 & code & wc & zs & n & Hf2 & Hv & Hina & Hft & Hcc & HTc & Hlz & Hndz & Hdz); eauto.
      pose proof Hv as Hvw.
      eapply (V_internal_fun cenv VT) in Hv; [| eapply not_exposed_internal_fun; eauto ].
      rewrite VT_dfn_eq in Hv. destruct Hv as (_ & lams & code' & wc' & _ & _ & HTc' & Hwc & Hb).
      rewrite HTc in HTc'. injection HTc' as Hc1 Hc2. subst code' wc'.
      assert (Hcode_in : Code code) by (eapply HT; eauto).
      unfold dispatch.
      eapply (E_target_step cenv (exposed.V cenv VT PG) P ex k _ _ _ _ _ HptP);
        [ intros; eapply wrap_case; eassumption |].
      eapply (E_projs_r cenv (exposed.V cenv VT PG) P ex k _ w c f vs2 zs _ rho2 HptP Hf2 Hndz).
      { intros Hc. eapply Hdz. constructor; [ exact Hc | left; left; constructor ]. }
      { eassumption. }
      intros rhop Hsp.
      intros r1 cin cout Hleq Hs. inv Hs.
      - exists OOT, cin, <0>. split; [ constructor; eassumption |].
        split; [ eapply HOOT; eassumption | exact I ].
      - inv H.
        match goal with [ H1 : M.get f rho1 = Some _ |- _ ] => rewrite Hf1 in H1; inv H1 end.
        match goal with
        | [ Ha : get_list ys rho1 = Some ?vs, Hb' : find_def _ _ = Some (w, ?xs, ?eb),
            Hc : set_lists ?xs ?vs _ = Some ?rhoc', Hd : bstep_fuel _ _ ?rhoc' ?eb _ _ _ |- _ ] =>
            rename Ha into Hgl; rename Hb' into Hfd; rename Hc into Hset; rename Hd into Hbd
        end.
        edestruct (G_get_list cenv VT PG k S rho1 rho2 ys _ HG Hys Hgl) as (args2 & Hgl2 & Hargs).
        edestruct (Hb _ args2 (k - 1) _ _ _ (Forall2_length _ _ _ Hargs) Hfd (eq_sym Hset))
          as (xs2 & e2 & rho2' & Hfd2 & Hs2 & Hbody).
        edestruct Hbody as (r2 & cin' & cout' & Hst & Hpost & HR);
          [ rewrite to_nat_add, to_nat_one_w in Hleq; lia
          | eapply (V_mono_Forall2 cenv VT); [ eassumption | lia ]
          | | rewrite Hw in Hbd; eassumption | ].
        { rewrite to_nat_add, to_nat_one_w in Hleq; lia. }
        exists r2, (cin' <+> one_w (Eapp code wc (zs ++ ys))), (cout' <+> one_w (Eapp code wc (zs ++ ys))).
        split; [| split ].
        + econstructor 2.
          * eapply BStept_app.
            -- rewrite <- (set_lists_not_In zs vs2 _ rhop code Hsp); [ eapply Hcode; eassumption |].
               intros Hc. eapply Hdz. constructor; [ exact Hc | now right ].
            -- eapply get_list_app.
               ++ eapply get_list_set_lists; eassumption.
               ++ erewrite get_list_set_lists_Disjoint; [ eassumption | | eassumption ].
                  eapply Disjoint_Included_r; [| eassumption ]. sets.
            -- eassumption.
            -- symmetry; eassumption.
            -- intros Hc; congruence.
            -- rewrite Hwc. eassumption.
          * intros Hex. eapply (proj1 (R_exposed cenv VT PG _ r1 r2 HR)).
            match goal with [ Hx : ex = true -> exposed_res r1 |- _ ] => exact (Hx Hex) end.
        + eapply Happ; eauto.
        + eapply (R_mono cenv VT); [ eassumption |]. rewrite to_nat_add, to_nat_one_w. lia.
    Qed.

    Lemma E_letapp_dfn ex k rho1 rho2 x f w ys e e' alts :
      exposedb w = false -> ~ Code x ->
      alts_ok L T Btop w alts (f |: FromList ys :|: occurs_free e) ->
      Gd k (occurs_free (Eletapp x f w ys e)) rho1 rho2 ->
      (forall m rho1' rho2', m < k -> Gd m (occurs_free e) rho1' rho2' -> E P ex m (e, rho1') (e', rho2')) ->
      E P ex k (Eletapp x f w ys e, rho1)
        (dispatch f w alts (fun code wc zs => Eletapp x code wc (zs ++ ys) e'), rho2).
    Proof.
      intros Hw Hx Halts Hgd Hcont.
      pose proof Hgd as (HG & Hbind & Hcode).
      pose proof Hprops as [Hcon Hproj Hfun Hchd Hctl Happ Hlet HletO HOOT Hbase HGP].
      assert (Hfin : occurs_free (Eletapp x f w ys e) f) by fv_mem.
      assert (Hys : FromList ys \subset occurs_free (Eletapp x f w ys e)) by (normalize_occurs_free; sets).
      assert (Hstuck : (forall rhoc B h, M.get f rho1 = Some (Vfun rhoc B h) -> fun_web B h = Some w -> False) ->
                       E P ex k (Eletapp x f w ys e, rho1)
                         (dispatch f w alts (fun code wc zs => Eletapp x code wc (zs ++ ys) e'), rho2)).
      { intros Hno r1 cin cout Hleq Hs. inv Hs.
        - exists OOT, cin, <0>. split; [ constructor; eapply lt_one_w; eassumption |].
          split; [ eapply HOOT; eassumption | exact I ].
        - inv H; exfalso; (eapply Hno; [ eassumption |]); unfold fun_web;
            match goal with [ Hd : find_def _ _ = Some _ |- _ ] => rewrite Hd end; reflexivity. }
      destruct (M.get f rho1) as [[ | rhoc B h | | ] |] eqn:Hf1; try (eapply Hstuck; intros; congruence).
      destruct (fun_web B h) as [w' |] eqn:Hfw; [| eapply Hstuck; intros; congruence ].
      destruct (peq w' w); [ subst | eapply Hstuck; intros; congruence ].
      edestruct (dispatch_lookup k (occurs_free (Eletapp x f w ys e)) rho1 rho2 f w (f |: FromList ys :|: occurs_free e) alts
                   (fun code wc zs => Eletapp x code wc (zs ++ ys) e') rhoc B h)
        as (c & vs2 & code & wc & zs & n & Hf2 & Hv & Hina & Hft & Hcc & HTc & Hlz & Hndz & Hdz); eauto.
      pose proof Hv as Hvw.
      eapply (V_internal_fun cenv VT) in Hv; [| eapply not_exposed_internal_fun; eauto ].
      rewrite VT_dfn_eq in Hv. destruct Hv as (_ & lams & code' & wc' & _ & _ & HTc' & Hwc & Hb).
      rewrite HTc in HTc'. injection HTc' as Hc1 Hc2. subst code' wc'.
      assert (Hcode_in : Code code) by (eapply HT; eauto).
      assert (Hwfvs : Forall wf_val vs2).
      { eapply (V_wf_r cenv VT) in Hvw. inv Hvw. eassumption. }
      unfold dispatch.
      eapply (E_target_step cenv (exposed.V cenv VT PG) P ex k _ _ _ _ _ HptP);
        [ intros; eapply wrap_case; eassumption |].
      eapply (E_projs_r cenv (exposed.V cenv VT PG) P ex k _ w c f vs2 zs _ rho2 HptP Hf2 Hndz).
      { intros Hc. eapply Hdz. constructor; [ exact Hc | left; left; left; constructor ]. }
      { eassumption. }
      intros rhop Hsp.
      assert (Hgdp : Gd k (Setminus _ (occurs_free e) [set x]) rho1 rhop).
      { eapply Gd_set_lists_r; [| | eassumption | eassumption ].
        - eapply Gd_antimon; [ eassumption |]. normalize_occurs_free. sets.
        - eapply Disjoint_Included_r; [| eassumption ]. intros z Hz. inv Hz.
          + inv H. left. right. eassumption.
          + right. eassumption. }
      intros r1 cin cout Hleq Hs. inv Hs.
      - exists OOT, cin, <0>. split; [ constructor; eassumption |].
        split; [ eapply HOOT; eassumption | exact I ].
      - assert (Hget_code : M.get code rhop = Some (Vfun rtop Btop code)).
        { rewrite <- (set_lists_not_In zs vs2 _ rhop code Hsp); [ eapply Hcode; eassumption |].
          intros Hc. eapply Hdz. constructor; [ exact Hc | now right ]. }
        inv H;
          (match goal with [ H1 : M.get f rho1 = Some _ |- _ ] => rewrite Hf1 in H1; inv H1 end;
           match goal with
           | [ Ha : get_list ys rho1 = Some ?vs, Hb' : find_def _ _ = Some (w, ?xs, ?eb),
               Hc : set_lists ?xs ?vs _ = Some ?rhoc' |- _ ] =>
               rename Ha into Hgl; rename Hb' into Hfd; rename Hc into Hset
           end;
           edestruct (G_get_list cenv VT PG k _ rho1 rho2 ys _ HG Hys Hgl) as (args2 & Hgl2 & Hargs);
           edestruct (Hb _ args2 (k - 1) _ _ _ (Forall2_length _ _ _ Hargs) Hfd (eq_sym Hset))
             as (xs2 & e2 & rho2' & Hfd2 & Hs2 & Hbody);
           assert (Hgl3 : get_list (zs ++ ys) rhop = Some (vs2 ++ args2));
           [ eapply get_list_app;
             [ eapply get_list_set_lists; eassumption
             | erewrite get_list_set_lists_Disjoint; [ eassumption | | eassumption ];
               eapply Disjoint_Included_r; [| eassumption ]; sets ] |]).
        + (* the call returns *)
          match goal with
          | [ Hbd : bstep_fuel _ (exposedb w) _ _ ?c1 (Res ?v) _,
              Hk : bstep_fuel _ ex (M.set x ?v rho1) e ?c2 r1 _ |- _ ] =>
              rename Hbd into Hbody1; rename Hk into Hk1
          end.
          edestruct Hbody as (r2 & cin' & cout' & Hst & Hpost & HR);
            [ rewrite !to_nat_add, to_nat_one_w in Hleq; lia
            | eapply (V_mono_Forall2 cenv VT); [ eassumption | lia ]
            | | rewrite Hw in Hbody1; eassumption | ].
          { rewrite !to_nat_add, to_nat_one_w in Hleq; lia. }
          destruct r2 as [| v2]; [ contradiction |]. simpl in HR.
          edestruct (Hcont (k - 1 - to_nat cin1) (M.set x v rho1) (M.set x v2 rhop))
            as (r3 & cin'' & cout'' & Hst3 & Hpost3 & HR3);
            [ rewrite !to_nat_add, to_nat_one_w in Hleq; lia
            | eapply Gd_set; [ eapply Gd_mono; [ exact Hgdp | lia ] | exact HR | exact Hx ]
            | | exact Hk1 | ].
          { rewrite !to_nat_add, to_nat_one_w in Hleq; lia. }
          exists r3, ((cin' <+> cin'') <+> one_w (Eletapp x code wc (zs ++ ys) e')),
                 ((cout' <+> cout'') <+> one_w (Eletapp x code wc (zs ++ ys) e')).
          split; [| split ].
          * econstructor 2.
            -- eapply BStept_letapp;
                 [ exact Hget_code | exact Hgl3 | exact Hfd2 | symmetry; exact Hs2
                 | intros Hc; congruence | rewrite Hwc; exact Hst | exact Hst3 ].
            -- intros Hex. eapply (proj1 (R_exposed cenv VT PG _ r1 r3 HR3)).
               match goal with [ Hx' : ex = true -> exposed_res r1 |- _ ] => exact (Hx' Hex) end.
          * eapply Hlet; eauto.
          * eapply (R_mono cenv VT); [ eassumption |]. rewrite !to_nat_add, to_nat_one_w. lia.
        + (* the call runs out of fuel *)
          match goal with
          | [ Hbd : bstep_fuel _ (exposedb w) _ _ _ OOT _ |- _ ] => rename Hbd into Hbody1
          end.
          edestruct Hbody as (r2 & cin' & cout' & Hst & Hpost & HR);
            [ rewrite !to_nat_add, to_nat_one_w in Hleq; lia
            | eapply (V_mono_Forall2 cenv VT); [ eassumption | lia ]
            | | rewrite Hw in Hbody1; eassumption | ].
          { rewrite !to_nat_add, to_nat_one_w in Hleq; lia. }
          destruct r2; [| contradiction ].
          exists OOT, (cin' <+> one_w (Eletapp x code wc (zs ++ ys) e')),
                 (cout' <+> one_w (Eletapp x code wc (zs ++ ys) e')).
          split; [| split ].
          * econstructor 2; [| intros; exact I ].
            eapply BStept_letapp_oot;
              [ exact Hget_code | exact Hgl3 | exact Hfd2 | symmetry; exact Hs2
              | intros Hc; congruence | rewrite Hwc; exact Hst ].
          * eapply HletO; eauto.
          * exact I.
    Qed.

    (** ** Fundamental property *)

    Lemma dfn_fundamental k :
      forall ex e e' rho1 rho2, trans e e' -> Gd k (occurs_free e) rho1 rho2 -> E P ex k (e, rho1) (e', rho2).
    Proof.
      induction k as [k IH] using lt_wf_rec.
      assert (IH' : IH_exp k) by (intros m ex e e' r1 r2 Hm; eapply IH; eauto).
      intros ex e e' rho1 rho2 Htr. revert ex rho1 rho2.
      induction Htr; intros ex rho1 rho2 Hgd; pose proof Hgd as (HG & Hbind & Hcode);
        pose proof Hprops as [Hcon Hproj Hfun Hchd Hctl Happ Hlet HletO HOOT Hbase HGP].
      - (* Econstr *)
        eapply (E_constr_compat cenv VT); eauto.
        + eapply (G_Forall2_var_rel cenv VT); eauto. normalize_occurs_free. sets.
        + intros m v1 v2 Hlt Hv. eapply IH; eauto. eapply Gd_set; eauto.
          eapply Gd_antimon; [ eapply Gd_mono; [ eassumption | lia ] |]. normalize_occurs_free. sets.
      - (* Eproj *)
        eapply (E_proj_compat cenv VT); eauto.
        + eapply (G_var_rel cenv VT); eauto. fv_mem.
        + intros m v1 v2 Hlt Hv. eapply IH; eauto. eapply Gd_set; eauto.
          eapply Gd_antimon; [ eapply Gd_mono; [ eassumption | lia ] |]. normalize_occurs_free. sets.
      - (* Ecase [] *)
        eapply (E_case_nil_compat cenv VT); eauto.
      - (* Ecase (_ :: _) *)
        eapply (E_case_cons_compat cenv VT); eauto.
        + eapply trans_case_tags; eauto.
        + eapply (G_var_rel cenv VT); eauto. fv_mem.
        + intros m Hlt. eapply IH; eauto.
          eapply Gd_antimon; [ eapply Gd_mono; [ eassumption | lia ] |]. normalize_occurs_free. sets.
        + eapply IHHtr2. eapply Gd_antimon; [ eassumption |]. normalize_occurs_free. sets.
      - (* Eletapp, exposed *)
        eapply (E_letapp_compat cenv VT); eauto.
        + eapply (var_rel_exposed_fun cenv VT); eauto. eapply (G_var_rel cenv VT); eauto. fv_mem.
        + eapply (G_Forall2_var_rel cenv VT); eauto. normalize_occurs_free. sets.
        + intros m v1 v2 Hlt _ Hv. eapply IH; eauto. eapply Gd_set; eauto.
          eapply Gd_antimon; [ eapply Gd_mono; [ eassumption | lia ] |]. normalize_occurs_free. sets.
      - (* Eletapp, internal *)
        eapply E_letapp_dfn; eauto.
      - (* Eapp, exposed *)
        eapply (E_app_compat cenv VT); eauto.
        + eapply (var_rel_exposed_fun cenv VT); eauto. eapply (G_var_rel cenv VT); eauto. fv_mem.
        + eapply (G_Forall2_var_rel cenv VT); eauto. normalize_occurs_free. sets.
      - (* Eapp, internal *)
        eapply E_app_dfn; eauto. fv_mem. normalize_occurs_free. sets.
      - (* Efun, exposed *)
        assert (Hnames : forall g, name_in_fundefs B g <-> name_in_fundefs B' g)
          by (eapply trans_fundefs_names; eauto).
        eapply (E_fun_compat cenv VT); eauto.
        eapply (E_mono cenv VT) with (k := k); [| lia ].
        eapply IHHtr. split; [| split ].
        + eapply (G_antimon cenv VT); [| eapply occurs_free_Efun_Included ].
          eapply (G_def_funs cenv VT).
          * eapply (G_antimon cenv VT); [ eassumption |].
            intros z [Hz Hn]. destruct Hz as [z Hz | z Hz]; [ exact Hz | contradiction ].
          * apply HG.
          * apply HG.
          * eassumption.
          * intros g Hg. eapply Vexp_dfn; eauto.
            eapply Gd_antimon; [ eassumption |]. eapply occurs_free_fundefs_Efun_Included.
        + intros z Hz. destruct (name_in_fundefs_dec B z) as [Hn | Hn].
          * rewrite def_funs_eq; eauto.
          * rewrite def_funs_neq; eauto. eapply Hbind. eapply occurs_free_Efun. right. constructor; eauto.
        + intros c Hc. rewrite def_funs_neq; eauto.
          intros Hn. match goal with [ Hd : Disjoint _ (name_in_fundefs B) Code |- _ ] => eapply Hd end.
          constructor; [ apply (proj2 (Hnames c)); eassumption | eassumption ].
      - (* Efun, internal *)
        eapply E_fun_int; eauto.
      - (* Eprim_val *)
        eapply (E_stuck_compat cenv VT); eauto. intros. eapply Eprim_val_stuck.
      - (* Eprim *)
        eapply (E_stuck_compat cenv VT); eauto. intros. eapply Eprim_stuck.
      - (* Ehalt *)
        eapply (E_halt_compat cenv VT); eauto. eapply (G_var_rel cenv VT); eauto. fv_mem.
    Qed.

  End WithTop.

  (** ** Top level *)

  Theorem dfn_correct e et : trans_top L T Btop e et -> E_web cenv P PG e et.
  Proof.
    intros (e' & -> & Htr & Hdis) k rho1 rho2 Htop Hb.
    assert (Hwf2 : wf_env rho2) by apply Htop.
    eapply (E_exposed_indep cenv (VT_dfn rho2) VT_web).
    eapply (E_target_step cenv _ P true k _ _ _ _ _ HptP); [ intros; eapply wrap_fun; eassumption |].
    eapply (dfn_fundamental rho2 Hwf2); eauto.
    pose proof (G_top_exposed_indep cenv VT_web (VT_dfn rho2) PG k _ rho1 rho2 Htop) as [HG _].
    split; [| split ].
    - split; [ apply HG | split; [ eapply wf_env_def_funs; eauto |] ].
      intros x Hx v1 Hget.
      edestruct (G_var_rel cenv (VT_dfn rho2) PG k _ rho1 rho2 x HG Hx v1 Hget) as (v2 & Hg2 & Hv).
      eexists; split; [| eassumption ]. rewrite def_funs_neq; [ eassumption |].
      intros Hc. eapply Hdis. constructor; eauto.
    - eassumption.
    - intros c Hc. rewrite def_funs_eq; eauto.
  Qed.

End DefuncRel.

(** * With the "target takes at least as many steps" postcondition *)

Section DefuncTop.

  Variable (cenv : term.ctor_env).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Variables (L : M.t (list ctor_tag)) (T : M.t (var * web * nat)) (Btop : fundefs).

  Hypothesis HT : forall c code wc n, T ! c = Some (code, wc, n) -> Code Btop code.
  Hypothesis HL :
    forall w lams, L ! w = Some lams ->
                   exists it, Forall (fun c => exists info, M.get c cenv = Some info /\
                                                            term.ctor_ind_tag info = it) lams.

  (** Defunctionalization is in the λweb relation, with postconditions that
      satisfy the requirements of the λweb pipeline ([web_post_prop]). *)
  Theorem dfn_correct_ge e et :
    trans_top L T Btop e et -> E_web cenv P_ge P_ge e et.
  Proof. eapply dfn_correct; eauto. eapply P_ge_properties. eapply P_ge_target_steps. Qed.

  Corollary dfn_post_prop :
    Post_properties cenv P_ge P_ge P_ge /\ post_upper_bound (P_ge : @exposed.PostT fuel trace).
  Proof. split; [ eapply P_ge_properties | eapply P_ge_upper_bound ]. Qed.

  (** Behavioral refinement of closed programs, including divergence
      preservation (the target takes at least as many steps). *)
  Corollary dfn_refines e et :
    closed_exp e -> trans_top L T Btop e et -> refines cenv value_ref e et.
  Proof.
    intros Hc Htr. eapply (E_web_refines cenv P_ge P_ge P_ge_upper_bound); eauto.
    eapply dfn_correct_ge; eauto.
  Qed.

End DefuncTop.
