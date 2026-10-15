(* MLton-style defunctionalization on λweb, after lambda lifting.

   The source program is expected to be lambda lifted: it starts with a
   bundle [Btop] of top-level code functions, and every function of a web
   selected for defunctionalization is a wrapper that calls a code function
   on its arguments and its free variables, as produced by CertiRocq's
   lambda lifting:

     let rec code_f xs zs = body   (* web wc, in Btop *)
     ...
     let rec f xs = code_f (xs ++ zs)   (* web w, selected *)

   A selected web [w] has a lambda set [WM.get w L] of constructor tags; the
   closure of a wrapper becomes a record [C_f(E)] ([T w] maps the tag [C_f]
   to [code_f]: tags need only be distinct within a web), and a call
   through [w] becomes a case analysis on the record over the lambda set,
   whose branches project the fields and call the code function by name.
   All the wrappers of a bundle share the fields [E] (the environment of
   the bundle, without its wrappers): a wrapper that
   captures a sibling (or itself) gets the sibling's record rebuilt from the
   same fields at the call, so mutually recursive closures need no cyclic
   records.  In the simple case of a single wrapper with no recursion:

     source                       target
     ------                       ------
     let rec f xs = code_f (xs ++ zs)
     and g ys = e_g               let rec g ys = let f = C_f(zs) in e_g'
     in e                         in let f = C_f(zs) in e'

     ... (f ys)_w ...             ... case_w f of
                                        | C_f(zs) => code_f (ys ++ zs)
                                        | C_h(zs) => code_h (ys ++ zs) ...

   Only the webs in [L] are defunctionalized: the other functions (in
   particular known functions and exposed ones) keep their calling
   convention, and a bundle may mix both kinds.  The continuation of a call
   whose result is bound ([Eletapp]) is either duplicated in the branches,
   or put in a join point, a local function called at the end of each
   branch.

   The target takes more steps than the source: a call through a selected
   web takes two steps in the source (the wrapper, then the code function)
   and a case analysis, the projections and one call in the target.  We use
   the postcondition [P_ge] (the target uses at least as much fuel as the
   source), which gives divergence preservation. *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics algebra set_util.
From CertiRocq.LambdaANF Require term term_util identifiers.
From CertiRocq.LambdaWeb Require Import syntax semantics exposed post compat select indep comp dpe.

Import ListNotations.

Open Scope alg_scope.

(** * Syntax of the transformation *)

(** The record of a wrapper: its name, web, tag and fields *)
Definition rec : Type := (var * web * ctor_tag * list var)%type.

Fixpoint bind_recs (rs : list rec) (e : exp) : exp :=
  match rs with
  | [] => e
  | (f, w, c, zs) :: rs => Econstr f w c zs (bind_recs rs e)
  end.

Definition rec_names (rs : list rec) : list var := map (fun '(f, _, _, _) => f) rs.

Definition rec_fields (rs : list rec) : list var := concat (map (fun '(_, _, _, zs) => zs) rs).

Fixpoint rec_of (rs : list rec) (f : var) : option (web * ctor_tag * list var) :=
  match rs with
  | [] => None
  | (g, w, c, zs) :: rs => if M.elt_eq f g then Some (w, c, zs) else rec_of rs f
  end.

(** The remaining functions of a bundle and the records of its wrappers *)
Definition fun_recs (B : fundefs) (rs : list rec) (e : exp) : exp :=
  match B, rs with
  | Fnil, _ :: _ => bind_recs rs e
  | _, _ => Efun B (bind_recs rs e)
  end.

(** Projecting the fields of a record *)
Fixpoint projs (zs : list var) (w : web) (c : ctor_tag) (n : N) (g : var) (e : exp) : exp :=
  match zs with
  | [] => e
  | z :: zs => Eproj z w c n g (projs zs w c (N.succ n) g e)
  end.

(** The extra arguments of a code function, as seen from the record of a
    wrapper.  All the wrappers of a bundle share the same fields (the
    environment [E] of the bundle, which contains no wrapper of the bundle):
    an argument is either a field of the environment, or the record of a
    sibling wrapper (its web and tag), rebuilt from the same fields.  This is
    how mutually recursive closures are represented without cyclic
    records. *)
Inductive arg : Type :=
| AEnv : nat -> arg
| ASib : web -> ctor_tag -> arg.

Definition arg_internal (a : arg) : Prop :=
  match a with AEnv _ => True | ASib w _ => exposedb w = false end.

(** Rebuild the sibling records [ss] from the projected fields [zs] *)
Fixpoint arg_binds (zs : list var) (args : list arg) (ss : list var) (e : exp) : exp :=
  match args, ss with
  | ASib w c :: args, s :: ss => Econstr s w c zs (arg_binds zs args ss e)
  | AEnv _ :: args, _ :: ss => arg_binds zs args ss e
  | _, _ => e
  end.

(** The variables holding the extra arguments *)
Fixpoint arg_vars (zs : list var) (args : list arg) (ss : list var) : list var :=
  match args, ss with
  | AEnv i :: args, _ :: ss =>
      match nth_error zs i with
      | Some z => z :: arg_vars zs args ss
      | None => arg_vars zs args ss
      end
  | ASib _ _ :: args, s :: ss => s :: arg_vars zs args ss
  | _, _ => []
  end.

(** Their values, given the fields of the record *)
Fixpoint arg_vals (vs : list val) (args : list arg) : option (list val) :=
  match args with
  | [] => Some []
  | AEnv i :: args =>
      match nth_error vs i, arg_vals vs args with
      | Some v, Some avs => Some (v :: avs)
      | _, _ => None
      end
  | ASib w c :: args =>
      match arg_vals vs args with
      | Some avs => Some (Vconstr w c vs :: avs)
      | None => None
      end
  end.

(** An alternative of a dispatch: the tag of a wrapper, its code function,
    the web of the code function, the variables receiving the fields, the
    extra arguments of the code function, and the variables receiving the
    rebuilt sibling records (one per argument). *)
Definition alt : Type := (ctor_tag * var * web * list var * list arg * list var)%type.

Definition alt_tag (a : alt) : ctor_tag := let '(c, _, _, _, _, _) := a in c.

Definition dispatch (g : var) (w : web) (alts : list alt) (call : var -> web -> list var -> exp) : exp :=
  Ecase g w (map (fun '(c, code, wc, zs, args, ss) =>
                    (c, projs zs w c 0 g (arg_binds zs args ss (call code wc (arg_vars zs args ss))))) alts).

Fixpoint fnames (B : fundefs) : list var :=
  match B with
  | Fcons f _ _ _ B => f :: fnames B
  | Fnil => []
  end.

Section Defunc.

  Variable (cenv : term.ctor_env).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Local Notation PostT := (@exposed.PostT fuel trace).
  Local Notation PostGT := (@exposed.PostGT fuel trace).

  (** ** The exposure flag *)

  Lemma bstep_fuel_ex_exposed ex rho e c r t :
    bstep_fuel cenv ex rho e c r t -> ex = true -> exposed_res r.
  Proof. intros H Hex; subst; eapply bstep_fuel_exposed; eauto. Qed.

  (** Evaluation with the exposure flag set also holds without it. *)
  Lemma bstep_fuel_unexposed ex rho e c r t :
    bstep_fuel cenv ex rho e c r t -> bstep_fuel cenv false rho e c r t.
  Proof.
    intros H.
    eapply (@bstep_fuel_ind' cenv fuel Hf trace Ht
              (fun _ rho e c r t => bstep cenv false rho e c r t)
              (fun _ rho e c r t => bstep_fuel cenv false rho e c r t)); eauto;
      intros; try (econstructor; eauto; fail).
    - econstructor 2; eauto. congruence.
  Qed.

  (** ** Target-only evaluation steps *)

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

  (** The target is at most one step behind the source *)
  Definition P_sh : PostT :=
    fun p1 p2 => match p1, p2 with (_, _, c1, _), (_, _, c2, _) => ge (c2 <+> one_w (Ehalt 1%positive)) c1 end.

  Lemma P_sh_target_steps : post_target_steps P_sh.
  Proof.
    intros until t2'. simpl. intros H Hc. eapply ge_trans; [| eassumption ].
    eapply ge_add; [ eassumption | eapply ge_refl ].
  Qed.

  (** One target step catches up *)
  Lemma E_target_step_sh (V : nat -> val -> val -> Prop) ex k p1 e2 rho2 e2' rho2' :
    (forall cin r cout,
        bstep_fuel cenv ex rho2' e2' cin r cout ->
        exists cout', bstep_fuel cenv ex rho2 e2 (cin <+> one_w e2) r cout') ->
    E' cenv V P_sh ex k p1 (e2', rho2') -> E' cenv V P_ge ex k p1 (e2, rho2).
  Proof.
    destruct p1 as [e1 rho1]. intros Hstep HE r1 cin cout Hleq Hs.
    edestruct HE as (r2 & cin2 & cout2 & Hs2 & HP & HR); eauto.
    edestruct Hstep as (cout' & Hs'); eauto.
    do 3 eexists. split; [ eassumption | split; [| eassumption ] ].
    simpl in *. rewrite (one_w_eq e2 (Ehalt 1%positive)). exact HP.
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
    exists cout', bstep_fuel cenv ex rho (Ecase y w cl) (cin <+> one_w (Ecase y w cl)) r cout'.
  Proof.
    intros Hget Hcc Hft Hs. eexists.
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

  (** ** Rebuilding the sibling records *)

  Fixpoint arg_set (vs : list val) (args : list arg) (ss : list var) (rho : env) : env :=
    match args, ss with
    | ASib w c :: args, s :: ss => arg_set vs args ss (M.set s (Vconstr w c vs) rho)
    | AEnv _ :: args, _ :: ss => arg_set vs args ss rho
    | _, _ => rho
    end.

  Lemma arg_set_frame vs args : forall ss rho x, ~ List.In x ss -> M.get x (arg_set vs args ss rho) = M.get x rho.
  Proof.
    induction args as [| [i | w c] args IH]; intros [| s ss] rho x Hx; simpl; eauto.
    - eapply IH. intros Hc; eapply Hx; now right.
    - rewrite IH; [| intros Hc; eapply Hx; now right ].
      rewrite M.gso; [ reflexivity | intros Hc; subst; eapply Hx; now left ].
  Qed.

  Lemma arg_set_wf vs args : forall ss rho,
    wf_env rho -> Forall wf_val vs -> Forall arg_internal args -> wf_env (arg_set vs args ss rho).
  Proof.
    induction args as [| [i | w c] args IH]; intros [| s ss] rho Hwf Hvs Hint; simpl; eauto; inv Hint; eauto.
    eapply IH; eauto. eapply wf_env_set; eauto. constructor; [ simpl in *; congruence | eassumption ].
  Qed.

  Lemma E_arg_binds_r (V : nat -> val -> val -> Prop) P ex k p1 zs vs e2
        (Hpt : post_target_steps P) :
    forall args ss rho2,
      get_list zs rho2 = Some vs ->
      Disjoint _ (FromList ss) (FromList zs) ->
      Forall arg_internal args ->
      E' cenv V P ex k p1 (e2, arg_set vs args ss rho2) ->
      E' cenv V P ex k p1 (arg_binds zs args ss e2, rho2).
  Proof.
    induction args as [| [i | w c] args IH]; intros [| s ss] rho2 Hg Hd Hint HE; simpl in *; eauto; inv Hint.
    - eapply IH; eauto. eapply Disjoint_Included_l; [| eassumption ]. intros z Hz; now right.
    - eapply E_target_step; [ eassumption | |].
      + intros. eapply wrap_constr; eauto. simpl in *. congruence.
      + eapply IH; [| | eassumption | eassumption ].
        * rewrite get_list_set_neq; [ eassumption |]. intros Hc. eapply Hd. constructor; [ now left | eassumption ].
        * eapply Disjoint_Included_l; [| eassumption ]. intros z Hz; now right.
  Qed.

  Lemma set_lists_nth_error (zs : list var) (vs : list val) (rho rho' : env) :
    NoDup zs -> set_lists zs vs rho = Some rho' ->
    forall i z, nth_error zs i = Some z -> M.get z rho' = nth_error vs i.
  Proof.
    revert vs rho'. induction zs as [| z0 zs IH]; intros vs rho' Hnd Hs i z Hz; [ destruct i; inv Hz |].
    destruct vs as [| v vs]; simpl in Hs; [ congruence |].
    destruct (set_lists zs vs rho) as [rho'' |] eqn:Hs'; [| congruence ]. inv Hs. inv Hnd.
    destruct i as [| i]; simpl in *.
    - inv Hz. rewrite M.gss. reflexivity.
    - rewrite M.gso; [ eapply IH; eauto |]. intros Hc; subst. eapply H1. eapply nth_error_In; eassumption.
  Qed.

  Lemma get_list_arg_vars (zs : list var) (vs : list val) (args : list arg) :
    forall ss rho avs,
      NoDup ss -> Disjoint _ (FromList ss) (FromList zs) -> length ss = length args ->
      length zs = length vs ->
      (forall i z, nth_error zs i = Some z -> M.get z rho = nth_error vs i) ->
      arg_vals vs args = Some avs ->
      get_list (arg_vars zs args ss) (arg_set vs args ss rho) = Some avs.
  Proof.
    induction args as [| [i | w c] args IH]; intros [| s ss] rho avs Hnd Hd Hlen Hlz Henv Hav;
      simpl in *; try congruence.
    - inv Hnd. destruct (nth_error vs i) as [v |] eqn:Hv; [| congruence ].
      destruct (arg_vals vs args) as [avs' |] eqn:Hav'; [| congruence ]. inv Hav.
      assert (Hi : i < length zs) by (rewrite Hlz; eapply nth_error_Some; congruence).
      destruct (nth_error zs i) as [z0 |] eqn:Hz; [| exfalso; eapply nth_error_Some; eassumption ].
      simpl. rewrite arg_set_frame.
      + rewrite (Henv _ _ Hz), Hv. erewrite IH; eauto.
        eapply Disjoint_Included_l; [| eassumption ]. intros z Hz'; now right.
      + intros Hc. eapply Hd. constructor; [ now right | eapply nth_error_In; eassumption ].
    - inv Hnd. destruct (arg_vals vs args) as [avs' |] eqn:Hav'; [| congruence ]. inv Hav.
      rewrite arg_set_frame; [| eassumption ]. rewrite M.gss. erewrite IH; eauto.
      + eapply Disjoint_Included_l; [| eassumption ]. intros z Hz'; now right.
      + intros i' z Hz. rewrite M.gso; [ eauto |]. intros Hc; subst.
        eapply Hd. constructor; [ now left | eapply nth_error_In; eassumption ].
  Qed.

  Lemma arg_vars_incl zs args ss z : List.In z (arg_vars zs args ss) -> List.In z zs \/ List.In z ss.
  Proof.
    revert ss. induction args as [| [i | w c] args IH]; intros [| s ss] Hz; simpl in *; try contradiction.
    - destruct (nth_error zs i) as [z' |] eqn:Hz'; [ destruct Hz as [Hz | Hz] |].
      + subst. left. eapply nth_error_In. eassumption.
      + destruct (IH ss Hz); [ now left | right; now right ].
      + destruct (IH ss Hz); [ now left | right; now right ].
    - destruct Hz as [Hz | Hz]; [ subst; right; now left |].
      destruct (IH ss Hz); [ now left | right; now right ].
  Qed.

  (** ** Records *)

  (** The environment after building records *)
  Inductive recs_env : list rec -> env -> env -> Prop :=
  | RE_nil : forall rho, recs_env [] rho rho
  | RE_cons : forall f w c zs rs vs rho rho',
      get_list zs rho = Some vs ->
      recs_env rs (M.set f (Vconstr w c vs) rho) rho' ->
      recs_env ((f, w, c, zs) :: rs) rho rho'.

  Definition recs_internal (rs : list rec) : Prop :=
    Forall (fun '(_, w, _, _) => exposedb w = false) rs.

  Lemma E_bind_recs_r (V : nat -> val -> val -> Prop) P ex k p1 e2
        (Hpt : post_target_steps P) :
    forall rs rho2,
      recs_internal rs ->
      (forall rho2', recs_env rs rho2 rho2' -> E' cenv V P ex k p1 (e2, rho2')) ->
      (exists rho2', recs_env rs rho2 rho2') ->
      E' cenv V P ex k p1 (bind_recs rs e2, rho2).
  Proof.
    induction rs as [| [[[f w] c] zs] rs IH]; intros rho2 Hint Hk [rho2' Hr]; simpl.
    - eapply Hk. inv Hr. constructor.
    - inv Hint. inv Hr. eapply E_target_step; [ eassumption | |].
      + intros. eapply wrap_constr; eauto. congruence.
      + eapply IH; eauto. intros. eapply Hk. econstructor; eauto.
  Qed.

  Lemma bstep_bind_recs ex e cin r cout :
    forall rs rho rho',
      recs_env rs rho rho' ->
      recs_internal rs ->
      bstep_fuel cenv ex rho' e cin r cout ->
      exists cin' cout', bstep_fuel cenv ex rho (bind_recs rs e) cin' r cout' /\
                         (rs = [] \/ ge cin' (cin <+> one_w (Ehalt 1%positive))) /\ ge cin' cin.
  Proof.
    intros rs rho rho' H. induction H; intros Hint Hs.
    - do 2 eexists. split; [ eassumption | split; [ now left | eapply ge_refl ] ].
    - inv Hint. edestruct IHrecs_env as (cin1 & cout1 & Hs1 & _ & Hge1); eauto.
      do 2 eexists. split; [| split ].
      + econstructor 2; [ econstructor; eauto; congruence |]. eapply bstep_fuel_ex_exposed; eauto.
      + right. rewrite (one_w_eq (bind_recs _ _) (Ehalt 1%positive)). eapply ge_add; eauto. eapply ge_refl.
      + eapply ge_trans; [ eapply ge_plus_r | eassumption ].
  Qed.

  Lemma rec_of_fields_aux rs f w c zs z :
    rec_of rs f = Some (w, c, zs) -> List.In z zs -> List.In z (rec_fields rs).
  Proof.
    unfold rec_fields. induction rs as [| [[[g w'] c'] zs'] rs IH]; simpl; intros H Hz; try congruence.
    eapply in_or_app. destruct (M.elt_eq f g); subst; [ inv H; now left | right; eauto ].
  Qed.

  Lemma recs_env_get_neq rs rho rho' x :
    recs_env rs rho rho' -> ~ List.In x (rec_names rs) -> M.get x rho' = M.get x rho.
  Proof.
    intros H. induction H; intros Hn; eauto. simpl in Hn.
    rewrite IHrecs_env; [| intros Hc; eapply Hn; now right ].
    rewrite M.gso; [ reflexivity | intros Hc; subst; eapply Hn; now left ].
  Qed.

  Lemma recs_env_get_eq rs rho rho' f w c zs :
    recs_env rs rho rho' -> NoDup (rec_names rs) ->
    Disjoint _ (FromList (rec_fields rs)) (FromList (rec_names rs)) ->
    rec_of rs f = Some (w, c, zs) ->
    exists vs, get_list zs rho = Some vs /\ M.get f rho' = Some (Vconstr w c vs).
  Proof.
    intros H. induction H; intros Hnd Hd Hr; simpl in *; try congruence. inv Hnd.
    destruct (M.elt_eq f f0); subst.
    - inv Hr. eexists. split; [ eassumption |].
      erewrite recs_env_get_neq; eauto. rewrite M.gss. reflexivity.
    - edestruct IHrecs_env as (vs' & Hg & Hff); eauto.
      + eapply Disjoint_Included; [| | eassumption ]; unfold rec_fields; simpl.
        * intros z Hz. now right.
        * intros z Hz. eapply in_or_app. now right.
      + eexists. split; [| eassumption ]. rewrite get_list_set_neq in Hg; eauto.
        intros Hc. eapply Hd. constructor; [| now left ].
        unfold rec_fields. simpl. eapply in_or_app. right.
        eapply (rec_of_fields_aux rs f w c zs f0); eauto.
  Qed.

  Lemma rec_of_In_aux rs f w c zs : rec_of rs f = Some (w, c, zs) -> List.In f (rec_names rs).
  Proof.
    induction rs as [| [[[g w'] c'] zs'] rs IH]; simpl; intros H; try congruence.
    destruct (M.elt_eq f g); subst; [ now left | right; eauto ].
  Qed.

  Lemma recs_env_exists rs rho :
    NoDup (rec_names rs) ->
    Disjoint _ (FromList (rec_fields rs)) (FromList (rec_names rs)) ->
    (forall f w c zs, rec_of rs f = Some (w, c, zs) -> exists vs, get_list zs rho = Some vs) ->
    exists rho', recs_env rs rho rho'.
  Proof.
    revert rho. induction rs as [| [[[f w] c] zs] rs IH]; intros rho Hnd Hd Hget.
    - eexists; constructor.
    - inv Hnd. edestruct (Hget f w c zs) as [vs Hvs]; [ simpl; destruct (M.elt_eq f f); congruence |].
      edestruct (IH (M.set f (Vconstr w c vs) rho)) as [rho' Hr]; eauto.
      + eapply Disjoint_Included; [| | eassumption ]; unfold rec_fields, rec_names; simpl.
        * intros z Hz. now right.
        * intros z Hz. eapply in_or_app. now right.
      + intros g w' c' zs' Hg. pose proof (rec_of_In_aux _ _ _ _ _ Hg) as Hin.
        assert (Hne : g <> f) by (intros Heq; subst; contradiction).
        edestruct (Hget g w' c' zs') as [vs' Hvs']; [ simpl; destruct (M.elt_eq g f); congruence |].
        exists vs'. rewrite get_list_set_neq; [ eassumption |].
        intros Hc. eapply Hd. constructor; [| now left ].
        unfold rec_fields. simpl. eapply in_or_app. right. eapply rec_of_fields_aux; eassumption.
      + eexists. econstructor; eauto.
  Qed.

  Lemma recs_env_wf rs rho rho' :
    recs_env rs rho rho' -> wf_env rho -> recs_internal rs -> wf_env rho'.
  Proof.
    intros H. induction H; intros Hwf Hint; eauto. inv Hint.
    eapply IHrecs_env; eauto. eapply wf_env_set; eauto. constructor.
    - intros Hc; congruence.
    - eapply wf_env_get_list; eauto.
  Qed.

End Defunc.

(** * Specification *)

(** The table of a defunctionalization: the record of tag [c] in web [w]
    stands for the closure of a wrapper that calls the code function
    [code] (of web [wc]) with [n] fields, passing the extra arguments
    [args].  Tags need only be distinct within a web: [T w] is a function
    of the tag. *)
Definition ctab : Type := web -> ctor_tag -> option (var * web * nat * list arg).

Section Spec.

  Variable (L : WM.t (list ctor_tag)).     (* lambda sets of the selected webs *)
  Variable (T : ctab).
  Variable (Btop : fundefs).              (* the lifted code functions *)

  Definition Code : Ensemble var := name_in_fundefs Btop.

  Definition alts_ok (w : web) (alts : list alt) (avoid : Ensemble var) : Prop :=
    WM.get w L = Some (map alt_tag alts) /\
    Forall (fun a => let '(c, code, wc, zs, args, ss) := a in
                     T w c = Some (code, wc, length zs, args) /\ NoDup (zs ++ ss) /\
                     length ss = length args /\ Forall arg_internal args /\
                     Disjoint _ (FromList (zs ++ ss)) (avoid :|: Code)) alts.

  (** An extra argument of a wrapper: a field of the environment [E] of the
      bundle, or a sibling wrapper (its record in [rs0], with the same
      fields). *)
  Definition arg_ok (E : list var) (rs0 : list rec) (a : arg) (z : var) : Prop :=
    match a with
    | AEnv i => nth_error E i = Some z
    | ASib w c => List.In (z, w, c, E) rs0
    end.

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
  | Trans_letapp_keep :
      forall x f w ys e e',
        keeps (sel_L L) w = true -> ~ Code x -> trans e e' ->
        trans (Eletapp x f w ys e) (Eletapp x f w ys e')
  (* the continuation is duplicated in the branches *)
  | Trans_letapp :
      forall x f w ys e e' alts,
        exposedb w = false -> ~ Code x ->
        alts_ok w alts (f |: FromList ys :|: occurs_free e) ->
        trans e e' ->
        trans (Eletapp x f w ys e)
              (dispatch f w alts (fun code wc zs => Eletapp x code wc (ys ++ zs) e'))
  (* the continuation is a join point [j] *)
  | Trans_letapp_join :
      forall x f w ys e e' alts j wj,
        exposedb w = false -> ~ Code x ->
        exposedb wj = false -> ~ Code j -> j <> x -> j <> f -> ~ List.In j ys -> ~ occurs_free e j ->
        alts_ok w alts (f |: FromList ys :|: [set j]) ->
        trans e e' ->
        trans (Eletapp x f w ys e)
              (Efun (Fcons j wj [x] e' Fnil)
                    (dispatch f w alts (fun code wc zs => Eletapp x code wc (ys ++ zs) (Eapp j wj [x]))))
  | Trans_app_keep :
      forall f w ys, keeps (sel_L L) w = true -> trans (Eapp f w ys) (Eapp f w ys)
  | Trans_app :
      forall f w ys alts,
        exposedb w = false ->
        alts_ok w alts (f |: FromList ys) ->
        trans (Eapp f w ys) (dispatch f w alts (fun code wc zs => Eapp code wc (ys ++ zs)))
  | Trans_fun :
      forall E B Bk rs e e',
        trans_bundle E rs B Bk rs ->
        NoDup (fnames B) ->
        Disjoint _ (name_in_fundefs B) Code ->
        Disjoint _ (FromList (rec_fields rs)) (FromList (rec_names rs)) ->
        FromList E \subset occurs_free_fundefs B :|: name_in_fundefs B ->
        trans e e' ->
        trans (Efun B e) (fun_recs Bk rs e')
  | Trans_prim_val :
      forall x p e e', ~ Code x -> trans e e' -> trans (Eprim_val x p e) (Eprim_val x p e')
  | Trans_prim :
      forall x p ys e e', ~ Code x -> trans e e' -> trans (Eprim x p ys e) (Eprim x p ys e')
  | Trans_halt : forall x, trans (Ehalt x) (Ehalt x)
  (* [trans_bundle E rs0 B Bk rs]: the functions [B] (a suffix of the bundle,
     whose records are [rs0], all with fields [E]) become the functions [Bk]
     and the records [rs] *)
  with trans_bundle : list var -> list rec -> fundefs -> fundefs -> list rec -> Prop :=
  | TB_nil : forall E rs0, trans_bundle E rs0 Fnil Fnil []
  | TB_keep :
      forall E rs0 f w xs e e' B Bk rs,
        keeps (sel_L L) w = true ->
        Disjoint _ (FromList xs) (Code :|: FromList (rec_fields rs0) :|: FromList (rec_names rs0)) ->
        trans e e' -> trans_bundle E rs0 B Bk rs ->
        trans_bundle E rs0 (Fcons f w xs e B) (Fcons f w xs (bind_recs rs0 e') Bk) rs
  | TB_sel :
      forall E rs0 f w xs zs B Bk rs lams c code wc args,
        exposedb w = false -> WM.get w L = Some lams -> List.In c lams ->
        T w c = Some (code, wc, length E, args) -> Code code ->
        exposedb wc = false -> WM.get wc L = None ->
        NoDup xs -> Disjoint _ (FromList xs) (FromList zs) -> ~ List.In code xs ->
        Forall2 (arg_ok E rs0) args zs ->
        trans_bundle E rs0 B Bk rs ->
        trans_bundle E rs0 (Fcons f w xs (Eapp code wc (xs ++ zs)) B) Bk ((f, w, c, E) :: rs).

  Scheme trans_mut := Induction for trans Sort Prop
  with trans_bundle_mut := Induction for trans_bundle Sort Prop.

  (** The whole program: the code functions are bound at the top, and are
      not defunctionalized. *)
  Definition trans_top (e : exp) (e_t : exp) : Prop :=
    exists e0 Btop' e0',
      e = Efun Btop e0 /\ e_t = Efun Btop' e0' /\
      trans_bundle [] [] Btop Btop' [] /\ NoDup (fnames Btop) /\ trans e0 e0'.

End Spec.

(** ** Syntactic facts *)

Section SpecFacts.

  Variables (L : WM.t (list ctor_tag)) (T : ctab) (Btop : fundefs).

  Local Notation Code := (Code Btop).
  Local Notation trans := (trans L T Btop).
  Local Notation trans_bundle := (trans_bundle L T Btop).

  Lemma trans_case_tags x w cl cl' :
    trans (Ecase x w cl) (Ecase x w cl') -> Forall2 (fun p p' => fst p = fst p') cl cl'.
  Proof.
    revert cl'. induction cl as [| [c e] cl IH]; intros cl' H; inv H; constructor; eauto.
  Qed.

  Lemma find_alt (g : var) (w : web) (alts : list alt) call c :
    List.In c (map alt_tag alts) ->
    exists code wc zs args ss n,
      List.In (c, code, wc, zs, args, ss) alts /\
      find_tag_nth (map (fun '(c, code, wc, zs, args, ss) =>
                           (c, projs zs w c 0 g (arg_binds zs args ss (call code wc (arg_vars zs args ss))))) alts)
                   c (projs zs w c 0 g (arg_binds zs args ss (call code wc (arg_vars zs args ss)))) n.
  Proof.
    induction alts as [| [[[[[c' code] wc] zs] args] ss] alts IH]; simpl; intros Hin; [ contradiction |].
    destruct (M.elt_eq c' c); subst.
    - do 6 eexists. split; [ now left | constructor ].
    - destruct Hin as [Heq | Hin]; [ congruence |].
      edestruct IH as (code'' & wc'' & zs'' & args'' & ss'' & n' & Hin' & Hft); eauto.
      do 6 eexists. split; [ now right; eauto | econstructor; eauto ].
  Qed.

  Lemma name_in_fnames B x : name_in_fundefs B x <-> List.In x (fnames B).
  Proof.
    induction B; simpl; split; intros H.
    - inv H; [ inv H0; now left | right; eapply IHB; eauto ].
    - destruct H; [ subst; left; constructor | right; eapply IHB; eauto ].
    - inv H.
    - contradiction.
  Qed.

  Lemma rec_of_In rs f w c zs : rec_of rs f = Some (w, c, zs) -> List.In f (rec_names rs).
  Proof.
    induction rs as [| [[[g w'] c'] zs'] rs IH]; simpl; intros H; try congruence.
    destruct (M.elt_eq f g); subst; [ now left | right; eauto ].
  Qed.

  Lemma rec_of_fields rs f w c zs z :
    rec_of rs f = Some (w, c, zs) -> List.In z zs -> List.In z (rec_fields rs).
  Proof.
    unfold rec_fields. induction rs as [| [[[g w'] c'] zs'] rs IH]; simpl; intros H Hz; try congruence.
    eapply in_or_app. destruct (M.elt_eq f g); subst; [ inv H; now left | right; eauto ].
  Qed.

  Lemma rec_names_rec_of rs f : List.In f (rec_names rs) -> exists w c zs, rec_of rs f = Some (w, c, zs).
  Proof.
    induction rs as [| [[[g w'] c'] zs'] rs IH]; simpl; intros H; [ contradiction |].
    destruct (M.elt_eq f g); subst; eauto. destruct H; [ congruence | eauto ].
  Qed.

  Lemma trans_bundle_names E rs0 B Bk rs :
    trans_bundle E rs0 B Bk rs ->
    forall f, name_in_fundefs B f <-> name_in_fundefs Bk f \/ List.In f (rec_names rs).
  Proof.
    intros H; induction H; intros g; simpl.
    - split; [ intros Hc; inv Hc | intros [Hc | Hc]; [ inv Hc | contradiction ] ].
    - specialize (IHtrans_bundle g). split.
      + intros Hg. destruct Hg as [g Hg | g Hg].
        * inv Hg. left. left. constructor.
        * apply IHtrans_bundle in Hg. destruct Hg; [ left; right; eassumption | now right ].
      + intros [Hg | Hg].
        * destruct Hg as [g Hg | g Hg]; [ left; eassumption | right; apply IHtrans_bundle; now left ].
        * right. apply IHtrans_bundle. now right.
    - specialize (IHtrans_bundle g). split.
      + intros Hg. destruct Hg as [g Hg | g Hg].
        * inv Hg. right. now left.
        * apply IHtrans_bundle in Hg. destruct Hg; [ now left | right; now right ].
      + intros [Hg | [Hg | Hg]].
        * right. apply IHtrans_bundle. now left.
        * subst. left. constructor.
        * right. apply IHtrans_bundle. now right.
  Qed.

  Lemma trans_bundle_internal E rs0 B Bk rs : trans_bundle E rs0 B Bk rs -> recs_internal rs.
  Proof. unfold recs_internal. intros H; induction H; eauto. Qed.

  Lemma trans_bundle_nodup E rs0 B Bk rs :
    trans_bundle E rs0 B Bk rs -> NoDup (fnames B) ->
    NoDup (rec_names rs) /\ Disjoint _ (name_in_fundefs Bk) (FromList (rec_names rs)).
  Proof.
    intros H.
    induction H as [E rs0 | E rs0 f w xs e e' B Bk rs Hk Hd0 Ht Hb IH
                   | E rs0 f w xs zs B Bk rs lams c code wc args Hw HL Hc HT HC Hwc HLwc Hnd0 Hdz Hcx Hargs Hb IH];
      simpl; intros Hnd.
    - split; [ constructor |]. constructor. intros z Hz. destruct Hz as [z Ha Ha']. inv Ha'.
    - inversion Hnd as [| f' l Hnin Hnd' Heq]; subst.
      destruct (IH Hnd') as [Hn Hd]. split; [ exact Hn |].
      constructor. intros z Hz. destruct Hz as [z Ha Ha']. destruct Ha as [z Ha | z Ha].
      + inv Ha. eapply Hnin. eapply name_in_fnames.
        eapply (proj2 (trans_bundle_names _ _ _ _ _ Hb z)). right. exact Ha'.
      + eapply Hd. constructor; eassumption.
    - inversion Hnd as [| f' l Hnin Hnd' Heq]; subst.
      destruct (IH Hnd') as [Hn Hd]. split.
      + constructor; [| exact Hn ]. intros Hcf. eapply Hnin. eapply name_in_fnames.
        eapply (proj2 (trans_bundle_names _ _ _ _ _ Hb f)). now right.
      + constructor. intros z Hz. destruct Hz as [z Ha Ha']. destruct Ha' as [Heq | Hin].
        * subst. eapply Hnin. eapply name_in_fnames.
          eapply (proj2 (trans_bundle_names _ _ _ _ _ Hb z)). now left.
        * eapply Hd. constructor; eassumption.
  Qed.

  Lemma trans_bundle_keep E rs0 B Bk rs f w xs e2 :
    trans_bundle E rs0 B Bk rs -> NoDup (fnames B) ->
    find_def f Bk = Some (w, xs, e2) ->
    exists e e',
      find_def f B = Some (w, xs, e) /\ e2 = bind_recs rs0 e' /\ trans e e' /\
      keeps (sel_L L) w = true /\
      Disjoint _ (FromList xs) (Code :|: FromList (rec_fields rs0) :|: FromList (rec_names rs0)).
  Proof.
    intros H.
    induction H as [E rs0 | E rs0 g w' xs' e e' B Bk rs Hk Hd0 Ht Hb IH
                   | E rs0 g w' xs' zs B Bk rs lams c code wc args Hw HL Hc HT HC Hwc HLwc Hnd0 Hdz Hcx Hargs Hb IH];
      simpl; intros Hnd Hf; try congruence;
      inversion Hnd as [| f' l Hnin Hnd' Heq]; subst.
    - destruct (M.elt_eq f g); subst; eauto.
      inv Hf. do 2 eexists. eauto 10.
    - destruct (M.elt_eq f g); subst; eauto.
      exfalso. eapply Hnin. eapply name_in_fnames.
      eapply (proj2 (trans_bundle_names _ _ _ _ _ Hb g)). left.
      eapply find_def_name_in_fundefs; eauto.
  Qed.

  Lemma trans_bundle_sel E rs0 B Bk rs f w c zs :
    trans_bundle E rs0 B Bk rs -> NoDup (fnames B) ->
    rec_of rs f = Some (w, c, zs) ->
    zs = E /\
    exists xs ys lams code wc args,
      find_def f B = Some (w, xs, Eapp code wc (xs ++ ys)) /\
      exposedb w = false /\ WM.get w L = Some lams /\ List.In c lams /\
      T w c = Some (code, wc, length E, args) /\ Code code /\
      exposedb wc = false /\ WM.get wc L = None /\
      NoDup xs /\ Disjoint _ (FromList xs) (FromList ys) /\ ~ List.In code xs /\
      Forall2 (arg_ok E rs0) args ys.
  Proof.
    intros H.
    induction H as [E rs0 | E rs0 g w' xs' e e' B Bk rs Hk Hd0 Ht Hb IH
                   | E rs0 g w' xs' zs' B Bk rs lams c' code wc args Hw HL Hc HT HC Hwc HLwc Hnd0 Hdz Hcx Hargs Hb IH];
      simpl; intros Hnd Hf; try congruence;
      inversion Hnd as [| f' l Hnin Hnd' Heq]; subst.
    - destruct (M.elt_eq f g); subst; eauto.
      exfalso. eapply Hnin. eapply name_in_fnames.
      eapply (proj2 (trans_bundle_names _ _ _ _ _ Hb g)). right. eapply rec_of_In; eauto.
    - destruct (M.elt_eq f g); subst; eauto.
      inv Hf. split; [ reflexivity |]. do 6 eexists. eauto 20.
  Qed.

  Lemma trans_bundle_fields E rs0 B Bk rs f w c zs :
    trans_bundle E rs0 B Bk rs -> List.In (f, w, c, zs) rs -> zs = E.
  Proof.
    intros H. induction H; simpl; intros Hin; try contradiction; eauto.
    destruct Hin as [Hin | Hin]; [ inv Hin; reflexivity | eauto ].
  Qed.

  Lemma rec_fields_E E rs0 B Bk rs z :
    trans_bundle E rs0 B Bk rs -> List.In z (rec_fields rs) -> List.In z E.
  Proof.
    intros H. induction H; simpl; intros Hin; try contradiction; eauto.
    unfold rec_fields in Hin. simpl in Hin. eapply in_app_or in Hin. destruct Hin; eauto.
  Qed.

  Lemma trans_bundle_names_sub E rs0 B Bk rs f :
    trans_bundle E rs0 B Bk rs -> name_in_fundefs Bk f -> name_in_fundefs B f.
  Proof. intros H Hf. eapply (proj2 (trans_bundle_names _ _ _ _ _ H f)). now left. Qed.

  Lemma In_rec_of rs f w c zs :
    NoDup (rec_names rs) -> List.In (f, w, c, zs) rs -> rec_of rs f = Some (w, c, zs).
  Proof.
    induction rs as [| [[[g w'] c'] zs'] rs IH]; simpl; intros Hnd Hin; [ contradiction |]. inv Hnd.
    destruct (M.elt_eq f g); subst.
    - destruct Hin as [Hin | Hin]; [ inv Hin; reflexivity |].
      exfalso. eapply H1. eapply in_map_iff. exists (g, w, c, zs). eauto.
    - destruct Hin as [Hin | Hin]; [ inv Hin; congruence | eauto ].
  Qed.

End SpecFacts.

(** * The logical relation *)

Section DefuncRel.

  Variable (cenv : term.ctor_env).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Local Notation PostT := (@exposed.PostT fuel trace).
  Local Notation PostGT := (@exposed.PostGT fuel trace).
  Local Notation VTransT := (@exposed.VTransT fuel trace).

  Variables (L : WM.t (list ctor_tag)) (T : ctab) (Btop Btop' : fundefs).

  Local Notation Code := (Code Btop).
  Local Notation trans := (trans L T Btop).
  Local Notation trans_bundle := (trans_bundle L T Btop).
  Local Notation sel := (sel_L L).

  (** The tags of a lambda set belong to the same inductive type *)
  Hypothesis HL :
    forall w lams, WM.get w L = Some lams ->
                   exists it, Forall (fun c => exists info, M.get c cenv = Some info /\
                                                            term.ctor_ind_tag info = it) lams.

  (** The closure of a wrapper is related to its record: the code function
      it calls is related to the target code function of the record's tag,
      and its extra arguments to the values rebuilt from the fields of the
      record (a field, or the record of a sibling wrapper with the same
      fields).  [rtop] is the environment of the target code functions. *)
  Definition VT_dfn (rtop : env) : VTransT :=
    fun PG V' k v1 v2 =>
      match v1, v2 with
      | Vfun rho1 B1 f1, Vconstr w c vs2 =>
          exists xs ys lams code wc args vcode vys avs,
            find_def f1 B1 = Some (w, xs, Eapp code wc (xs ++ ys)) /\
            WM.get w L = Some lams /\ List.In c lams /\ T w c = Some (code, wc, length vs2, args) /\
            exposedb wc = false /\ WM.get wc L = None /\
            NoDup xs /\ Disjoint _ (FromList xs) (FromList ys) /\ ~ List.In code xs /\
            M.get code (def_funs B1 B1 rho1 rho1) = Some vcode /\
            get_list ys (def_funs B1 B1 rho1 rho1) = Some vys /\
            arg_vals vs2 args = Some avs /\
            (forall j, j < k -> V' j vcode (Vfun rtop Btop' code) /\ Forall2 (V' j) vys avs)
      | _, _ => False
      end.

  Global Instance VTransProps_dfn rtop : VTransProps (VT_dfn rtop).
  Proof.
    constructor; unfold VT_dfn.
    - intros PG V1 V2 k v1 v2 Hext. destruct v1, v2; try easy.
      intros (xs & ys & lams & code & wc & args & vcode & vys & avs & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13).
      exists xs, ys, lams, code, wc, args, vcode, vys, avs. repeat (split; [ eassumption |]).
      intros j Hj. destruct (H13 j Hj) as [Hc Hz]. split.
      + eapply Hext; eauto.
      + eapply Forall2_monotonic; [| eassumption ]. intros. eapply Hext; eauto.
    - intros PG V k j v1 v2 Hmono. destruct v1, v2; try easy.
      intros (xs & ys & lams & code & wc & args & vcode & vys & avs & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13) Hle.
      exists xs, ys, lams, code, wc, args, vcode, vys, avs. repeat (split; [ eassumption |]).
      intros i Hi. eapply H13. lia.
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
    WM.get w L = Some (map alt_tag alts) -> List.In c (map alt_tag alts) ->
    term_util.caseConsistent cenv
      (erase_branches (map (fun '(c, code, wc, zs, args, ss) =>
                              (c, projs zs w c 0 g (arg_binds zs args ss (call code wc (arg_vars zs args ss))))) alts)) c.
  Proof.
    intros HLw Hin. eapply caseConsistent_lams; eauto.
    clear. induction alts as [| [[[[[c code] wc] zs] args] ss] alts IH]; simpl; constructor.
    - simpl. now left.
    - eapply Forall_impl; [| exact IH ]. intros p Hp. now right.
  Qed.

  (** The code functions of the tags are defined at the top *)
  Hypothesis HT : forall w c code wc n args, T w c = Some (code, wc, n, args) -> Code code.

  Lemma sel_L_None w : WM.get w L = None -> sel w = false.
  Proof. unfold sel_L. intros H; rewrite H; reflexivity. Qed.

  Lemma keeps_unsel w : WM.get w L = None -> keeps sel w = true.
  Proof. intros H. unfold keeps. rewrite sel_L_None; [| eassumption ]. apply orb_true_r. Qed.

  Section WithTop.

    Context (rtop : env) (Hrtop : wf_env rtop).

    Local Notation VT := (VT_sel cenv sel (VT_dfn rtop)).
    Local Notation V := (V cenv VT P_ge).
    Local Notation E := (E cenv VT P_ge).
    Local Notation G := (G cenv VT P_ge).
    Local Notation var_rel := (var_rel cenv VT P_ge).

    Ltac fuel_arith :=
      repeat match goal with
             | [ H : context [ to_nat (_ <+> _) ] |- _ ] => rewrite to_nat_add in H
             | [ |- context [ to_nat (_ <+> _) ] ] => rewrite to_nat_add
             | [ H : context [ to_nat (one_w _) ] |- _ ] => rewrite to_nat_one_w in H
             | [ |- context [ to_nat (one_w _) ] ] => rewrite to_nat_one_w
             end; lia.

    Ltac one_w_norm :=
      repeat match goal with
             | [ |- context [ @one_w fuel _ ?e ] ] =>
                 tryif unify e (Ehalt 1%positive) then fail
                 else rewrite (one_w_eq e (Ehalt 1%positive))
             end.

    (** Unpacking the relation of a wrapper and its record *)
    Lemma V_rec_inv k rhoc B h w c vs2 xs e :
      V k (Vfun rhoc B h) (Vconstr w c vs2) ->
      find_def h B = Some (w, xs, e) -> exposedb w = false -> sel w = true ->
      exists ys lams code wc args vcode vys avs,
        e = Eapp code wc (xs ++ ys) /\
        WM.get w L = Some lams /\ List.In c lams /\ T w c = Some (code, wc, length vs2, args) /\
        exposedb wc = false /\ WM.get wc L = None /\
        NoDup xs /\ Disjoint _ (FromList xs) (FromList ys) /\ ~ List.In code xs /\
        M.get code (def_funs B B rhoc rhoc) = Some vcode /\
        get_list ys (def_funs B B rhoc rhoc) = Some vys /\
        arg_vals vs2 args = Some avs /\
        (forall j, j < k -> V j vcode (Vfun rtop Btop' code) /\ Forall2 (V j) vys avs).
    Proof.
      intros Hv Hfd Hw Hs.
      eapply (V_sel_internal cenv sel (VT_dfn rtop) P_ge) in Hv; [| eassumption | eassumption | eassumption ].
      destruct Hv as (xs' & ys & lams & code & wc & args & vcode & vys & avs & Hfd' & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13).
      rewrite Hfd in Hfd'. inv Hfd'. exists ys, lams, code, wc, args, vcode, vys, avs. eauto 20.
    Qed.

    (** ** Calls through a selected web, once the record is decoded *)

    Lemma E_app_core ex k rho1 rhop f w ys c vs2 code wc args avs zs' :
      exposedb w = false -> sel w = true ->
      (forall rhoc B h, M.get f rho1 = Some (Vfun rhoc B h) -> fun_web B h = Some w ->
                        V k (Vfun rhoc B h) (Vconstr w c vs2)) ->
      T w c = Some (code, wc, length vs2, args) -> arg_vals vs2 args = Some avs ->
      M.get code rhop = Some (Vfun rtop Btop' code) ->
      get_list zs' rhop = Some avs ->
      Forall2 (var_rel k rho1 rhop) ys ys ->
      E P_sh ex k (Eapp f w ys, rho1) (Eapp code wc (ys ++ zs'), rhop).
    Proof.
      intros Hw Hsel Hv HTc Hav Hcode Hzs Hys r1 cin cout Hleq Hs. inv Hs.
      - exists OOT, cin, <0>. split; [ constructor; eapply lt_one_w; eassumption |].
        split; [ simpl; eapply ge_plus_r | exact I ].
      - match goal with [ Hx : ex = true -> exposed_res r1 |- _ ] => rename Hx into Hexr end.
        inv H.
        match goal with
        | [ Hg : M.get f rho1 = Some (Vfun ?rc ?B ?h), Hfd : find_def ?h ?B = Some (w, ?xs, ?eb),
            Hgl : get_list ys rho1 = Some ?vs, Hset : set_lists ?xs ?vs _ = Some ?rc',
            Hb : bstep_fuel _ (exposedb w) ?rc' ?eb _ _ _ |- _ ] =>
            rename Hg into Hf1; rename Hfd into Hfd1; rename Hgl into Hgl1; rename Hset into Hset1;
            rename Hb into Hbody1
        end.
        edestruct (V_rec_inv k) as (zs & lams & code' & wc' & args' & vcode & vzs & avs' & Heb & HLw & Hinc & HTc' &
                                    Hwc & HLwc & Hndx & Hdxz & Hcx & Hgc & Hgz & Hav' & Hrel);
          [ eapply Hv; [ eassumption | unfold fun_web; rewrite Hfd1; reflexivity ] | eassumption | eassumption | eassumption |].
        subst. assert (Heqs : code' = code /\ wc' = wc /\ args' = args) by (rewrite HTc in HTc'; inv HTc'; auto).
          destruct Heqs as (-> & -> & ->). rewrite Hav in Hav'. injection Hav' as Heqa. subst avs'.
        rewrite Hw in Hbody1. inv Hbody1.
        + (* the wrapper runs out of fuel *)
          exists OOT, cin0, <0>. split; [ constructor; eapply lt_one_w; eassumption |].
          split; [ simpl; one_w_norm; eapply ge_refl | exact I ].
        + match goal with [ Hx : false = true -> exposed_res r1 |- _ ] => clear Hx end.
          inv H.
          match goal with
          | [ Hg : M.get code _ = Some (Vfun ?rt ?Bt ?g), Hfd : find_def ?g ?Bt = Some (wc, ?xs1, ?e1),
              Hgl : get_list (xs ++ zs) _ = Some ?vs', Hset : set_lists ?xs1 ?vs' _ = Some ?r1',
              Hb : bstep_fuel _ (exposedb wc) ?r1' ?e1 _ _ _ |- _ ] =>
              rename Hg into Hgc1; rename Hfd into Hfd2; rename Hgl into Hgl2; rename Hset into Hset2;
              rename Hb into Hbody2
          end.
          (* the code closure and the arguments of the inner call *)
          rewrite <- (set_lists_not_In _ _ _ _ code Hset1 Hcx), Hgc in Hgc1. inv Hgc1.
          assert (Hgl' : get_list (xs ++ zs) rhoc' = Some (vs ++ vzs)).
          { eapply get_list_app; [ eapply get_list_set_lists; eassumption |].
            erewrite get_list_set_lists_Disjoint; [ eassumption | eassumption | eassumption ]. }
          rewrite Hgl' in Hgl2. inv Hgl2.
          edestruct var_rel_get_list as (args2 & Hga & Hargs); [ eassumption | eassumption |].
          assert (Hk : 2 <= k) by fuel_arith.
          destruct (Hrel (k - 1) ltac:(lia)) as [Hvc Hvz].
          eapply (V_keeps_fun cenv sel (VT_dfn rtop) P_ge) in Hvc;
            [| unfold fun_web; rewrite Hfd2; reflexivity | eapply keeps_unsel; eassumption ].
          edestruct (Hvc (vs ++ vzs) (args2 ++ avs) (k - 2)) as (xs2 & e2 & rho2' & Hfd3 & Hset3 & Hbody);
            [ rewrite !length_app; f_equal; [ eapply Forall2_length; eassumption | eapply Forall2_length; eassumption ]
            | eassumption | symmetry; eassumption |].
          edestruct Hbody as (r2 & cin2 & cout2 & Hst2 & Hpost & HR);
            [ lia | rewrite Hwc; congruence
            | eapply Forall2_app; [ eapply (V_mono_Forall2 cenv VT); [ eassumption | lia ]
                                  | eapply (V_mono_Forall2 cenv VT); [ eassumption | lia ] ]
            | | first [ exact Hbody2 | rewrite Hwc in Hbody2; exact Hbody2 | rewrite Hwc; exact Hbody2 ] |]; [ fuel_arith |].
          exists r2, (cin2 <+> one_w (Eapp code wc (ys ++ zs'))), (cout2 <+> one_w (Eapp code wc (ys ++ zs'))).
          split; [| split ].
          * econstructor 2.
            -- eapply BStept_app; [ eassumption | eapply get_list_app; eassumption | eassumption
                                  | symmetry; eassumption | intros Hc; rewrite Hwc in Hc; congruence | eassumption ].
            -- intros Hex. eapply (proj1 (R_exposed cenv VT P_ge _ r1 r2 HR)). eauto.
          * simpl in *. one_w_norm. eapply ge_add; [ eapply ge_add; [ eassumption | eapply ge_refl ] | eapply ge_refl ].
          * eapply (R_mono cenv VT); [ eassumption |]. fuel_arith.
    Qed.

    Lemma ge_letapp_sh (c1 c2 d1 d2 u1 u2 u3 u4 : fuel) :
      ge c2 c1 -> ge d2 d1 -> u1 = u2 -> u2 = u3 -> u3 = u4 ->
      ge (((c2 <+> d2) <+> u1) <+> u2) (((c1 <+> u3) <+> d1) <+> u4).
    Proof.
      intros H1 H2 -> -> ->.
      replace ((c1 <+> u4) <+> d1) with ((c1 <+> d1) <+> u4).
      - eapply ge_add; [ eapply ge_add; [ eapply ge_add; eassumption | eapply ge_refl ] | eapply ge_refl ].
      - rewrite !plus_assoc. f_equal. apply plus_comm.
    Qed.

    Lemma E_letapp_core ex k rho1 rhop x f w ys e e' c vs2 code wc args avs zs' :
      exposedb w = false -> sel w = true ->
      (forall rhoc B h, M.get f rho1 = Some (Vfun rhoc B h) -> fun_web B h = Some w ->
                        V k (Vfun rhoc B h) (Vconstr w c vs2)) ->
      T w c = Some (code, wc, length vs2, args) -> arg_vals vs2 args = Some avs ->
      M.get code rhop = Some (Vfun rtop Btop' code) ->
      get_list zs' rhop = Some avs ->
      Forall2 (var_rel k rho1 rhop) ys ys ->
      (forall m v1 v2, m < k -> V m v1 v2 -> E P_ge ex m (e, M.set x v1 rho1) (e', M.set x v2 rhop)) ->
      E P_sh ex k (Eletapp x f w ys e, rho1) (Eletapp x code wc (ys ++ zs') e', rhop).
    Proof.
      intros Hw Hsel Hv HTc Hav Hcode Hzs Hys Hcont r1 cin cout Hleq Hs. inv Hs.
      - exists OOT, cin, <0>. split; [ constructor; eapply lt_one_w; eassumption |].
        split; [ simpl; eapply ge_plus_r | exact I ].
      - match goal with [ Hx : ex = true -> exposed_res r1 |- _ ] => rename Hx into Hexr end.
        inv H.
        + (* the call returns *)
          match goal with
          | [ Hg : M.get f rho1 = Some (Vfun ?rc ?B ?h), Hfd : find_def ?h ?B = Some (w, ?xs, ?eb),
              Hgl : get_list ys rho1 = Some ?vs, Hset : set_lists ?xs ?vs _ = Some ?rc',
              Hb : bstep_fuel _ (exposedb w) ?rc' ?eb _ _ _,
              Hk : bstep_fuel _ ex (M.set x _ rho1) e _ _ _ |- _ ] =>
              rename Hg into Hf1; rename Hfd into Hfd1; rename Hgl into Hgl1; rename Hset into Hset1;
              rename Hb into Hbody1; rename Hk into Hk1
          end.
          edestruct (V_rec_inv k) as (zs & lams & code' & wc' & args' & vcode & vzs & avs' & Heb & HLw & Hinc & HTc' &
                                      Hwc & HLwc & Hndx & Hdxz & Hcx & Hgc & Hgz & Hav' & Hrel);
            [ eapply Hv; [ eassumption | unfold fun_web; rewrite Hfd1; reflexivity ] | eassumption | eassumption | eassumption |].
          subst. assert (Heqs : code' = code /\ wc' = wc /\ args' = args) by (rewrite HTc in HTc'; inv HTc'; auto).
          destruct Heqs as (-> & -> & ->). rewrite Hav in Hav'. injection Hav' as Heqa. subst avs'.
          rewrite Hw in Hbody1. inv Hbody1.
          match goal with [ Hx : false = true -> exposed_res _ |- _ ] => clear Hx end.
          inv H.
          match goal with
          | [ Hg : M.get code _ = Some (Vfun ?rt ?Bt ?g), Hfd : find_def ?g ?Bt = Some (wc, ?xs1, ?e1),
              Hgl : get_list (xs ++ zs) _ = Some ?vs', Hset : set_lists ?xs1 ?vs' _ = Some ?r1',
              Hb : bstep_fuel _ (exposedb wc) ?r1' ?e1 _ _ _ |- _ ] =>
              rename Hg into Hgc1; rename Hfd into Hfd2; rename Hgl into Hgl2; rename Hset into Hset2;
              rename Hb into Hbody2
          end.
          rewrite <- (set_lists_not_In _ _ _ _ code Hset1 Hcx), Hgc in Hgc1. inv Hgc1.
          assert (Hgl' : get_list (xs ++ zs) rhoc' = Some (vs ++ vzs)).
          { eapply get_list_app; [ eapply get_list_set_lists; eassumption |].
            erewrite get_list_set_lists_Disjoint; [ eassumption | eassumption | eassumption ]. }
          rewrite Hgl' in Hgl2. inv Hgl2.
          edestruct var_rel_get_list as (args2 & Hga & Hargs); [ eassumption | eassumption |].
          assert (Hk : 2 <= k) by fuel_arith.
          destruct (Hrel (k - 1) ltac:(lia)) as [Hvc Hvz].
          eapply (V_keeps_fun cenv sel (VT_dfn rtop) P_ge) in Hvc;
            [| unfold fun_web; rewrite Hfd2; reflexivity | eapply keeps_unsel; eassumption ].
          edestruct (Hvc (vs ++ vzs) (args2 ++ avs) (k - 2)) as (xs2 & e2 & rho2' & Hfd3 & Hset3 & Hbody);
            [ rewrite !length_app; f_equal; [ eapply Forall2_length; eassumption | eapply Forall2_length; eassumption ]
            | eassumption | symmetry; eassumption |].
          edestruct Hbody as (r2 & cb2 & tb2 & Hst2 & Hpost & HR);
            [ lia | rewrite Hwc; congruence
            | eapply Forall2_app; [ eapply (V_mono_Forall2 cenv VT); [ eassumption | lia ]
                                  | eapply (V_mono_Forall2 cenv VT); [ eassumption | lia ] ]
            | | first [ exact Hbody2 | rewrite Hwc in Hbody2; exact Hbody2 | rewrite Hwc; exact Hbody2 ] |];
            [ fuel_arith |].
          destruct r2 as [| v2]; [ contradiction |]. simpl in HR.
          match type of HR with
          | exposed.V _ _ _ ?i _ _ =>
              edestruct (Hcont i) as (r3 & ck & tk & Hst3 & Hpost3 & HR3);
                [ lia | eassumption | | eassumption | ]; [ fuel_arith |]
          end.
          match goal with
          | [ Hb : bstep_fuel _ (exposedb wc) rho2' e2 ?cb (Res v2) ?tb |- _ ] =>
              exists r3, ((cb <+> ck) <+> one_w (Eletapp x code wc (ys ++ zs') e')),
                     ((tb <+> tk) <+> one_w (Eletapp x code wc (ys ++ zs') e'))
          end.
          split; [| split ].
          * econstructor 2.
            -- eapply BStept_letapp; [ eassumption | eapply get_list_app; eassumption | eassumption
                                     | symmetry; eassumption | intros Hc; rewrite Hwc in Hc; congruence
                                     | eassumption | eassumption ].
            -- intros Hex. eapply (proj1 (R_exposed cenv VT P_ge _ r1 r3 HR3)). eauto.
          * simpl in *. eapply ge_letapp_sh; eauto; eapply one_w_eq.
          * eapply (R_mono cenv VT); [ eassumption |]. fuel_arith.
        + (* the call runs out of fuel *)
          match goal with
          | [ Hg : M.get f rho1 = Some (Vfun ?rc ?B ?h), Hfd : find_def ?h ?B = Some (w, ?xs, ?eb),
              Hgl : get_list ys rho1 = Some ?vs, Hset : set_lists ?xs ?vs _ = Some ?rc',
              Hb : bstep_fuel _ (exposedb w) ?rc' ?eb _ OOT _ |- _ ] =>
              rename Hg into Hf1; rename Hfd into Hfd1; rename Hgl into Hgl1; rename Hset into Hset1;
              rename Hb into Hbody1
          end.
          edestruct (V_rec_inv k) as (zs & lams & code' & wc' & args' & vcode & vzs & avs' & Heb & HLw & Hinc & HTc' &
                                      Hwc & HLwc & Hndx & Hdxz & Hcx & Hgc & Hgz & Hav' & Hrel);
            [ eapply Hv; [ eassumption | unfold fun_web; rewrite Hfd1; reflexivity ] | eassumption | eassumption | eassumption |].
          subst. assert (Heqs : code' = code /\ wc' = wc /\ args' = args) by (rewrite HTc in HTc'; inv HTc'; auto).
          destruct Heqs as (-> & -> & ->). rewrite Hav in Hav'. injection Hav' as Heqa. subst avs'.
          rewrite Hw in Hbody1. inv Hbody1.
          * exists OOT, cin0, <0>. split; [ constructor; eapply lt_one_w; eassumption |].
            split; [ simpl; one_w_norm; eapply ge_refl | exact I ].
          * match goal with [ Hx : false = true -> exposed_res _ |- _ ] => clear Hx end.
            inv H.
            match goal with
            | [ Hg : M.get code _ = Some (Vfun ?rt ?Bt ?g), Hfd : find_def ?g ?Bt = Some (wc, ?xs1, ?e1),
                Hgl : get_list (xs ++ zs) _ = Some ?vs', Hset : set_lists ?xs1 ?vs' _ = Some ?r1',
                Hb : bstep_fuel _ (exposedb wc) ?r1' ?e1 _ _ _ |- _ ] =>
                rename Hg into Hgc1; rename Hfd into Hfd2; rename Hgl into Hgl2; rename Hset into Hset2;
                rename Hb into Hbody2
            end.
            rewrite <- (set_lists_not_In _ _ _ _ code Hset1 Hcx), Hgc in Hgc1. inv Hgc1.
            assert (Hgl' : get_list (xs ++ zs) rhoc' = Some (vs ++ vzs)).
            { eapply get_list_app; [ eapply get_list_set_lists; eassumption |].
              erewrite get_list_set_lists_Disjoint; [ eassumption | eassumption | eassumption ]. }
            rewrite Hgl' in Hgl2. inv Hgl2.
            edestruct var_rel_get_list as (args2 & Hga & Hargs); [ eassumption | eassumption |].
            assert (Hk : 2 <= k) by fuel_arith.
            destruct (Hrel (k - 1) ltac:(lia)) as [Hvc Hvz].
            eapply (V_keeps_fun cenv sel (VT_dfn rtop) P_ge) in Hvc;
              [| unfold fun_web; rewrite Hfd2; reflexivity | eapply keeps_unsel; eassumption ].
            edestruct (Hvc (vs ++ vzs) (args2 ++ avs) (k - 2)) as (xs2 & e2 & rho2' & Hfd3 & Hset3 & Hbody);
              [ rewrite !length_app; f_equal; [ eapply Forall2_length; eassumption | eapply Forall2_length; eassumption ]
              | eassumption | symmetry; eassumption |].
            edestruct Hbody as (r2 & cin2 & cout2 & Hst2 & Hpost & HR);
              [ lia | rewrite Hwc; congruence
              | eapply Forall2_app; [ eapply (V_mono_Forall2 cenv VT); [ eassumption | lia ]
                                    | eapply (V_mono_Forall2 cenv VT); [ eassumption | lia ] ]
              | | first [ exact Hbody2 | rewrite Hwc in Hbody2; exact Hbody2 | rewrite Hwc; exact Hbody2 ] |];
              [ fuel_arith |].
            destruct r2; [| contradiction ].
            exists OOT, (cin2 <+> one_w (Eletapp x code wc (ys ++ zs') e')),
                   (cout2 <+> one_w (Eletapp x code wc (ys ++ zs') e')).
            split; [| split ].
            -- econstructor 2; [| intros; exact I ].
               eapply BStept_letapp_oot; [ eassumption | eapply get_list_app; eassumption | eassumption
                                         | symmetry; eassumption | intros Hc; rewrite Hwc in Hc; congruence
                                         | eassumption ].
            -- simpl in *. one_w_norm.
               eapply ge_add; [ eapply ge_add; [ eassumption | eapply ge_refl ] | eapply ge_refl ].
            -- exact I.
    Qed.

    (** ** Join points *)

    Lemma E_join_call ex m e rho1 e' rhoJ j wj x v2 rho2 :
      exposedb wj = false ->
      M.get j rho2 = Some (Vfun rhoJ (Fcons j wj [x] e' Fnil) j) ->
      M.get x rho2 = Some v2 ->
      E P_ge false m (e, rho1) (e', M.set x v2 (def_funs (Fcons j wj [x] e' Fnil) (Fcons j wj [x] e' Fnil) rhoJ rhoJ)) ->
      E P_ge ex m (e, rho1) (Eapp j wj [x], rho2).
    Proof.
      intros Hwj Hj Hx HE r1 cin cout Hleq Hs.
      edestruct HE as (r2 & cin2 & cout2 & Hs2 & HP & HR); [ eassumption | eapply bstep_fuel_unexposed; eassumption |].
      exists r2, (cin2 <+> one_w (Eapp j wj [x])), (cout2 <+> one_w (Eapp j wj [x])).
      split; [| split ].
      - econstructor 2.
        + eapply BStept_app; [ eassumption | simpl; rewrite Hx; reflexivity | simpl; destruct (M.elt_eq j j); [ reflexivity | congruence ]
                             | reflexivity | intros Hc; congruence | rewrite Hwj; eassumption ].
        + intros Hex. subst. eapply (proj1 (R_exposed cenv VT P_ge _ r1 r2 HR)).
          eapply bstep_fuel_exposed; eassumption.
      - eapply P_ge_target_steps; [ eassumption | eapply ge_plus_r ].
      - eassumption.
    Qed.

    (** ** Environments *)

    Definition code_env (rho : env) := forall c, Code c -> M.get c rho = Some (Vfun rtop Btop' c).

    Definition Gd k S rho1 rho2 :=
      G k S rho1 rho2 /\ term_util.binding_in_map S rho1 /\ code_env rho2.

    Definition IH_exp k :=
      forall m ex e e' rho1 rho2,
        m < k -> trans e e' -> Gd m (occurs_free e) rho1 rho2 -> E P_ge ex m (e, rho1) (e', rho2).

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

    Lemma Gd_set_r k S rho1 rho2 x v :
      Gd k S rho1 rho2 -> wf_val v -> ~ S x -> ~ Code x -> Gd k S rho1 (M.set x v rho2).
    Proof.
      intros (HG & Hb & Hc) Hv Hx Hcx. split; [ eapply (G_set_r_not_in cenv VT); eauto | split; eauto ].
      intros c Hcc. rewrite M.gso; eauto. intros Heq; subst; eauto.
    Qed.

    Lemma Gd_set_lists_r k S rho1 rho2 rho2' zs vs :
      Gd k S rho1 rho2 -> Disjoint _ (FromList zs) (S :|: Code) -> Forall wf_val vs ->
      set_lists zs vs rho2 = Some rho2' -> Gd k S rho1 rho2'.
    Proof.
      intros (HG & Hb & Hc) Hd Hwf Hs. split; [| split; [ exact Hb |] ].
      - split; [ apply HG | split; [ eapply wf_env_set_lists; [ apply HG | eassumption | eassumption ] |] ].
        intros x Hx v1 Hget. edestruct (G_var_rel cenv VT P_ge k S rho1 rho2 x HG Hx v1 Hget) as (v2 & Hg2 & Hv).
        eexists; split; [| exact Hv ]. rewrite <- (set_lists_not_In zs vs _ rho2' x Hs); [ exact Hg2 |].
        intros Hin. eapply Hd. constructor; [ exact Hin | now left ].
      - intros c Hcc. rewrite <- (set_lists_not_In zs vs _ rho2' c Hs); [ eauto |].
        intros Hin. eapply Hd. constructor; [ exact Hin | now right ].
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

    Lemma Forall2_var_rel_set_lists_r_gen k rho1 rho2 rhop ys1 ys zs vs :
      Forall2 (var_rel k rho1 rho2) ys1 ys -> Disjoint _ (FromList zs) (FromList ys) ->
      set_lists zs vs rho2 = Some rhop -> Forall2 (var_rel k rho1 rhop) ys1 ys.
    Proof.
      intros Hall Hd Hs. induction Hall; constructor.
      - intros v1 Hg. edestruct H as (v2 & Hg2 & Hv); eauto. eexists; split; eauto.
        rewrite <- (set_lists_not_In _ _ _ _ _ Hs); eauto.
        intros Hc. eapply Hd. constructor; [ eassumption | now left ].
      - eapply IHHall. eapply Disjoint_Included_r; [| eassumption ]. intros z Hz. now right.
    Qed.

    Lemma Forall2_var_rel_set_lists_r k rho1 rho2 rhop ys zs vs :
      Forall2 (var_rel k rho1 rho2) ys ys -> Disjoint _ (FromList zs) (FromList ys) ->
      set_lists zs vs rho2 = Some rhop -> Forall2 (var_rel k rho1 rhop) ys ys.
    Proof. eapply Forall2_var_rel_set_lists_r_gen. Qed.

    Lemma get_list_pointwise (R : val -> val -> Prop) zs rhoA rhoB :
      (forall z, List.In z zs -> exists v1 v2, M.get z rhoA = Some v1 /\ M.get z rhoB = Some v2 /\ R v1 v2) ->
      exists vs1 vs2, get_list zs rhoA = Some vs1 /\ get_list zs rhoB = Some vs2 /\ Forall2 R vs1 vs2.
    Proof.
      induction zs as [| z zs IH]; intros Hz.
      - do 2 eexists; split; [ reflexivity | split; [ reflexivity | constructor ] ].
      - edestruct (Hz z) as (v1 & v2 & H1 & H2 & H3); [ now left |].
        edestruct IH as (vs1 & vs2 & H4 & H5 & H6); [ intros; eapply Hz; now right |].
        exists (v1 :: vs1), (v2 :: vs2). simpl. rewrite H1, H2, H4, H5. eauto.
    Qed.

    (** ** Calls through a selected web *)

    Lemma NoDup_app_disj {A} (l1 l2 : list A) : NoDup (l1 ++ l2) -> Disjoint _ (FromList l1) (FromList l2).
    Proof.
      induction l1 as [| x l1 IH]; simpl; intros Hnd; constructor; intros z Hz; destruct Hz as [z Hz1 Hz2].
      - inv Hz1.
      - inv Hnd. destruct Hz1 as [Hz1 | Hz1].
        + subst. eapply H1. eapply in_or_app. now right.
        + eapply (IH H2). constructor; eassumption.
    Qed.

    Lemma E_dispatch ex k e1 rho1 rho2 f w alts call avoid :
      exposedb w = false ->
      alts_ok L T Btop w alts avoid -> avoid f -> wf_env rho2 ->
      (forall (cin : fuel) r (cout : trace), bstep_fuel cenv ex rho1 e1 cin r cout ->
                          (r = OOT /\ cin << one_w e1) \/
                          ((exists c' : fuel, cin = algebra.plus c' (one_w e1)) /\
                           exists rhoc B h, M.get f rho1 = Some (Vfun rhoc B h) /\ fun_web B h = Some w)) ->
      var_rel k rho1 rho2 f f ->
      (forall c vs2 code wc zs args ss avs rhop,
          List.In (c, code, wc, zs, args, ss) alts ->
          M.get f rho2 = Some (Vconstr w c vs2) ->
          (forall rhoc B h, M.get f rho1 = Some (Vfun rhoc B h) -> fun_web B h = Some w ->
                            V k (Vfun rhoc B h) (Vconstr w c vs2)) ->
          T w c = Some (code, wc, length vs2, args) ->
          arg_vals vs2 args = Some avs ->
          Disjoint _ (FromList (zs ++ ss)) (avoid :|: Code) ->
          (forall x, ~ List.In x (zs ++ ss) -> M.get x rhop = M.get x rho2) ->
          wf_env rhop ->
          get_list (arg_vars zs args ss) rhop = Some avs ->
          E P_sh ex k (e1, rho1) (call code wc (arg_vars zs args ss), rhop)) ->
      E P_ge ex k (e1, rho1) (dispatch f w alts call, rho2).
    Proof.
      intros Hw [HLw Halts] Hfa Hwfr2 Hstuck Hvf Hk r1 cin cout Hleq Hs.
      destruct (Hstuck _ _ _ Hs) as [[-> Hoot] | ((c' & ->) & rhoc & B & h & Hf1 & Hfw)].
      - exists OOT, cin, <0>. split; [ constructor; eapply lt_one_w; eassumption |].
        split; [ simpl; eapply ge_refl | exact I ].
      - edestruct Hvf as (v2 & Hf2 & Hv); [ eassumption |].
        unfold fun_web in Hfw. destruct (find_def h B) as [[[w' xs] eb] |] eqn:Hfd; [ injection Hfw as -> | discriminate ].
        assert (Hk1 : 1 <= k) by (rewrite to_nat_add, to_nat_one_w in Hleq; lia).
        assert (Hsel : sel w = true) by (eapply sel_L_Some; eassumption).
        pose proof Hv as Hv'.
        eapply (V_sel_internal cenv sel (VT_dfn rtop) P_ge) in Hv; [| eassumption | eassumption | eassumption ].
        destruct v2 as [w2 c vs2 | | |]; try contradiction.
        destruct Hv as (xs' & ys0 & lams & code0 & wc0 & args0 & vcode & vys & avs & Hfd' & HLw' & Hinc & HTc0 & _ & _ & _ & _ & _ & _ & _ & Hav & _).
        rewrite Hfd in Hfd'. injection Hfd' as Hw2 Hxs Heb. subst w2 xs'. rewrite HLw in HLw'. injection HLw' as Hlams. subst lams.
        edestruct (find_alt f w alts call c) as (code & wc & zs & args & ss & n & Hina & Hft); [ eassumption |].
        pose proof Halts as Halts'. eapply Forall_forall in Halts'; [| exact Hina ].
        destruct Halts' as (HTc & Hnd & Hlss & Hint & Hdz).
        assert (Heqs : code0 = code /\ wc0 = wc /\ length vs2 = length zs /\ args0 = args)
          by (rewrite HTc0 in HTc; inv HTc; auto).
        destruct Heqs as (-> & -> & Hlen & ->).
        assert (Hwf2 : Forall wf_val vs2).
        { eapply (V_wf_r cenv VT) in Hv'. inv Hv'. eassumption. }
        assert (Hndz : NoDup zs) by (eapply NoDup_app_remove_r; eassumption).
        assert (Hnds : NoDup ss) by (eapply NoDup_app_remove_l; eassumption).
        assert (Hdzs : Disjoint _ (FromList zs) (FromList ss)) by (eapply NoDup_app_disj; eassumption).
        assert (HE : E P_ge ex k (e1, rho1) (dispatch f w alts call, rho2)).
        { unfold dispatch.
          eapply (E_target_step_sh cenv (exposed.V cenv VT P_ge) ex k _ _ _
                    (projs zs w c 0 f (arg_binds zs args ss (call code wc (arg_vars zs args ss)))) rho2).
          { intros. eapply wrap_case; [ eassumption | eapply dispatch_cc; eauto | eassumption | eassumption ]. }
          eapply (E_projs_r cenv (exposed.V cenv VT P_ge) P_sh ex k _ w c f vs2 zs _ rho2 P_sh_target_steps Hf2 Hndz).
          { intros Hc. eapply Hdz. constructor; [ eapply in_or_app; left; exact Hc | left; exact Hfa ]. }
          { symmetry; exact Hlen. }
          intros rhop0 Hsp.
          eapply (E_arg_binds_r cenv (exposed.V cenv VT P_ge) P_sh ex k _ zs vs2 _ P_sh_target_steps);
            [ eapply get_list_set_lists; eassumption | eapply Disjoint_sym; eassumption | eassumption |].
          eapply Hk; eauto.
          - intros rhoc' B' h' Hf1' Hfw'. rewrite Hf1 in Hf1'. inv Hf1'. eassumption.
          - intros x Hx. rewrite arg_set_frame; [| intros Hc; eapply Hx; eapply in_or_app; now right ].
            rewrite <- (set_lists_not_In _ _ _ _ _ Hsp); [ reflexivity |].
            intros Hc; eapply Hx; eapply in_or_app; now left.
          - eapply arg_set_wf; [ eapply wf_env_set_lists; eassumption | eassumption | eassumption ].
          - eapply get_list_arg_vars; [ eassumption | eapply Disjoint_sym; eassumption | eassumption
                                      | congruence | | eassumption ].
            eapply set_lists_nth_error; eassumption. }
        eapply HE; eauto.
    Qed.

    Lemma stuck_app ex rho f w ys (cin : fuel) r (cout : trace) :
      bstep_fuel cenv ex rho (Eapp f w ys) cin r cout ->
      (r = OOT /\ cin << one_w (Eapp f w ys)) \/
      ((exists c' : fuel, cin = algebra.plus c' (one_w (Eapp f w ys))) /\
       exists rhoc B h, M.get f rho = Some (Vfun rhoc B h) /\ fun_web B h = Some w).
    Proof.
      intros Hs. inv Hs; [ left; eauto | right ]. split; [ eauto |].
      inv H. do 3 eexists. split; [ eassumption | unfold fun_web ].
      match goal with [ Hd : find_def _ _ = Some _ |- _ ] => rewrite Hd end. reflexivity.
    Qed.

    Lemma stuck_letapp ex rho x f w ys e (cin : fuel) r (cout : trace) :
      bstep_fuel cenv ex rho (Eletapp x f w ys e) cin r cout ->
      (r = OOT /\ cin << one_w (Eletapp x f w ys e)) \/
      ((exists c' : fuel, cin = algebra.plus c' (one_w (Eletapp x f w ys e))) /\
       exists rhoc B h, M.get f rho = Some (Vfun rhoc B h) /\ fun_web B h = Some w).
    Proof.
      intros Hs. inv Hs; [ left; eauto | right ]. split; [ eauto |].
      inv H; do 3 eexists; (split; [ eassumption | unfold fun_web ]);
        match goal with [ Hd : find_def _ _ = Some _ |- _ ] => rewrite Hd end; reflexivity.
    Qed.

    Lemma rhop_code k S rho1 rho2 rhop X code :
      Gd k S rho1 rho2 -> Code code -> Disjoint _ (FromList X) Code ->
      (forall x, ~ List.In x X -> M.get x rhop = M.get x rho2) ->
      M.get code rhop = Some (Vfun rtop Btop' code).
    Proof.
      intros (_ & _ & Hc) Hcc Hd Hfr. rewrite Hfr; eauto.
      intros Hin. eapply Hd. constructor; eauto.
    Qed.

    Lemma Forall2_var_rel_frame k rho1 rho2 rhop ys1 ys X :
      Forall2 (var_rel k rho1 rho2) ys1 ys -> Disjoint _ (FromList X) (FromList ys) ->
      (forall x, ~ List.In x X -> M.get x rhop = M.get x rho2) ->
      Forall2 (var_rel k rho1 rhop) ys1 ys.
    Proof.
      intros Hall Hd Hfr. induction Hall; constructor.
      - intros v1 Hg. edestruct H as (v2 & Hg2 & Hv); [ exact Hg |]. exists v2. split; [| exact Hv ].
        rewrite Hfr; [ exact Hg2 |]. intros Hc. eapply Hd. constructor; [ eassumption | now left ].
      - eapply IHHall. eapply Disjoint_Included_r; [| eassumption ]. intros z Hz. now right.
    Qed.

    Lemma Gd_frame k S rho1 rho2 rhop X :
      Gd k S rho1 rho2 -> Disjoint _ (FromList X) (S :|: Code) ->
      (forall x, ~ List.In x X -> M.get x rhop = M.get x rho2) -> wf_env rhop ->
      Gd k S rho1 rhop.
    Proof.
      intros (HG & Hb & Hc) Hd Hfr Hwf. split; [| split; [ exact Hb |] ].
      - split; [ apply HG | split; [ exact Hwf |] ].
        intros x Hx v1 Hget. edestruct (G_var_rel cenv VT P_ge k S rho1 rho2 x HG Hx v1 Hget) as (v2 & Hg2 & Hv).
        eexists; split; [| exact Hv ]. rewrite Hfr; [ exact Hg2 |].
        intros Hin. eapply Hd. constructor; [ exact Hin | now left ].
      - intros c Hcc. rewrite Hfr; [ eauto |].
        intros Hin. eapply Hd. constructor; [ exact Hin | now right ].
    Qed.

    Lemma arg_vars_avoid zs args ss (S : Ensemble var) :
      Disjoint _ (FromList (zs ++ ss)) S -> forall z, List.In z (arg_vars zs args ss) -> ~ S z.
    Proof.
      intros Hd z Hz Hs. eapply Hd. constructor; [| eassumption ].
      eapply in_or_app. eapply arg_vars_incl. eassumption.
    Qed.

    Lemma E_app_dfn ex k rho1 rho2 f w ys alts :
      exposedb w = false ->
      alts_ok L T Btop w alts (f |: FromList ys) ->
      Gd k (occurs_free (Eapp f w ys)) rho1 rho2 ->
      E P_ge ex k (Eapp f w ys, rho1) (dispatch f w alts (fun code wc zs => Eapp code wc (ys ++ zs)), rho2).
    Proof.
      intros Hw Halts Hgd. pose proof Hgd as (HG & Hb & Hc).
      eapply E_dispatch; [ eassumption | eassumption | now left | apply HG | | |].
      - intros. eapply stuck_app; eauto.
      - eapply (G_var_rel cenv VT); eauto. fv_mem.
      - intros c vs2 code wc zs args ss avs rhop Hin Hf2 Hv HTc Hav Hdz Hfr Hwfp Hga.
        eapply E_app_core; eauto.
        + destruct Halts as [HLw _]. eapply sel_L_Some; eassumption.
        + eapply rhop_code; eauto. eapply Disjoint_Included_r; [| eassumption ]. sets.
        + eapply Forall2_var_rel_frame; [| | eassumption ].
          * eapply (G_Forall2_var_rel cenv VT); eauto. normalize_occurs_free. sets.
          * eapply Disjoint_Included_r; [| eassumption ]. sets.
    Qed.

    Lemma E_letapp_dfn ex k rho1 rho2 x f w ys e e' alts :
      exposedb w = false -> ~ Code x ->
      alts_ok L T Btop w alts (f |: FromList ys :|: occurs_free e) ->
      Gd k (occurs_free (Eletapp x f w ys e)) rho1 rho2 ->
      (forall m rho1' rho2', m < k -> Gd m (occurs_free e) rho1' rho2' -> E P_ge ex m (e, rho1') (e', rho2')) ->
      E P_ge ex k (Eletapp x f w ys e, rho1)
        (dispatch f w alts (fun code wc zs => Eletapp x code wc (ys ++ zs) e'), rho2).
    Proof.
      intros Hw Hx Halts Hgd Hcont. pose proof Hgd as (HG & Hb & Hc).
      eapply E_dispatch; [ eassumption | eassumption | left; left; constructor | apply HG | | |].
      - intros. eapply stuck_letapp; eauto.
      - eapply (G_var_rel cenv VT); eauto. fv_mem.
      - intros c vs2 code wc zs args ss avs rhop Hin Hf2 Hv HTc Hav Hdz Hfr Hwfp Hga.
        eapply E_letapp_core; eauto.
        + destruct Halts as [HLw _]. eapply sel_L_Some; eassumption.
        + eapply rhop_code; eauto. eapply Disjoint_Included_r; [| eassumption ]. sets.
        + eapply Forall2_var_rel_frame; [| | eassumption ].
          * eapply (G_Forall2_var_rel cenv VT); eauto. normalize_occurs_free. sets.
          * eapply Disjoint_Included_r; [| eassumption ]. sets.
        + intros m v1 v2 Hlt Hv12. eapply Hcont; [ eassumption |].
          eapply Gd_set; [| eassumption | eassumption ].
          eapply Gd_frame; [| | eassumption | eassumption ].
          * eapply Gd_antimon; [ eapply Gd_mono; [ eassumption | lia ] |]. normalize_occurs_free. sets.
          * eapply Disjoint_Included_r; [| eassumption ]. intros z Hz. inv Hz.
            -- inv H. left. right. eassumption.
            -- right. eassumption.
    Qed.

    Lemma E_letapp_join_dfn ex k rho1 rho2 x f w ys e e' alts j wj :
      exposedb w = false -> ~ Code x ->
      exposedb wj = false -> ~ Code j -> j <> x -> j <> f -> ~ List.In j ys -> ~ occurs_free e j ->
      alts_ok L T Btop w alts (f |: FromList ys :|: [set j]) ->
      Gd k (occurs_free (Eletapp x f w ys e)) rho1 rho2 ->
      (forall m rho1' rho2', m < k -> Gd m (occurs_free e) rho1' rho2' -> E P_ge false m (e, rho1') (e', rho2')) ->
      E P_ge ex k (Eletapp x f w ys e, rho1)
        (Efun (Fcons j wj [x] e' Fnil)
              (dispatch f w alts (fun code wc zs => Eletapp x code wc (ys ++ zs) (Eapp j wj [x]))), rho2).
    Proof.
      intros Hw Hx Hwj Hj Hjx Hjf Hjys Hje Halts Hgd Hcont. pose proof Hgd as (HG & Hb & Hc).
      set (J := Fcons j wj [x] e' Fnil).
      assert (HJ : def_funs J J rho2 rho2 = M.set j (Vfun rho2 J j) rho2) by reflexivity.
      assert (Hgd' : Gd k (occurs_free (Eletapp x f w ys e)) rho1 (def_funs J J rho2 rho2)).
      { rewrite HJ. eapply Gd_set_r; eauto.
        - constructor. apply HG.
        - intros Hin. apply (proj1 (occurs_free_Eletapp x f w ys e)) in Hin.
          destruct Hin as [z Hin | z Hin].
          + destruct Hin as [z Hin | z Hin]; [ inv Hin; congruence | contradiction ].
          + destruct Hin as [Hin _]. eapply Hje. exact Hin. }
      eapply E_target_step; [ eapply P_ge_target_steps | intros; eapply wrap_fun; eassumption |].
      eapply E_dispatch; [ eassumption | eassumption | left; left; constructor | apply Hgd' | | |].
      - intros. eapply stuck_letapp; eauto.
      - eapply (G_var_rel cenv VT); [ apply Hgd' | fv_mem ].
      - intros c vs2 code wc zs args ss avs rhop Hin Hf2 Hv HTc Hav Hdz Hfr Hwfp Hga.
        eapply E_letapp_core; eauto.
        + destruct Halts as [HLw _]. eapply sel_L_Some; eassumption.
        + eapply rhop_code; [ exact Hgd' | | | eassumption ]; eauto.
          eapply Disjoint_Included_r; [| eassumption ]. sets.
        + eapply Forall2_var_rel_frame; [| | eassumption ].
          * eapply (G_Forall2_var_rel cenv VT); [ apply Hgd' |]. normalize_occurs_free. sets.
          * eapply Disjoint_Included_r; [| eassumption ]. sets.
        + intros m v1 v2 Hlt Hv12.
          eapply E_join_call; [ eassumption | | rewrite M.gss; reflexivity | ].
          * rewrite M.gso; [| congruence ].
            rewrite Hfr; [ rewrite HJ, M.gss; reflexivity |].
            intros Hinj. eapply Hdz. constructor; [ eassumption | left; right; constructor ].
          * eapply Hcont; [ eassumption |].
            eapply Gd_set; [| eassumption | eassumption ].
            fold J. rewrite HJ. eapply Gd_set_r; [| constructor; apply HG | | eassumption ].
            -- eapply Gd_antimon; [ eapply Gd_mono; [ eassumption | lia ] |]. normalize_occurs_free. sets.
            -- intros Hjin. destruct Hjin as [Hjin _]. eapply Hje. exact Hjin.
    Qed.

    (** ** Bundles: kept closures and records of wrappers (Löb induction) *)

    Lemma not_exposed_record w c vs : exposedb w = false -> ~ exposed_val (Vconstr w c vs).
    Proof. intros Hw Hexp. rewrite exposed_val_Vconstr in Hexp. destruct Hexp. congruence. Qed.

    Lemma get_list_nth_error (xs : list var) (vs : list val) rho i x :
      get_list xs rho = Some vs -> nth_error xs i = Some x -> M.get x rho = nth_error vs i.
    Proof.
      revert vs i. induction xs as [| y xs IH]; intros vs i Hg Hx; [ destruct i; inv Hx |].
      simpl in Hg. destruct (M.get y rho) eqn:Hy; [| congruence ].
      destruct (get_list xs rho) eqn:Hxs; [| congruence ]. inv Hg.
      destruct i; simpl in *; [ inv Hx; exact Hy | eauto ].
    Qed.

    Lemma Forall2_nth_error_l {A B} (R : A -> B -> Prop) l1 l2 i a :
      Forall2 R l1 l2 -> nth_error l1 i = Some a -> exists b, nth_error l2 i = Some b /\ R a b.
    Proof.
      intros H. revert i. induction H; intros i Hi; [ destruct i; inv Hi |].
      destruct i; simpl in *; [ inv Hi; eauto | eauto ].
    Qed.

    Lemma V_bundle k rho1 rho2 E B Bk rs :
      trans_bundle E rs B Bk rs ->
      NoDup (fnames B) ->
      (rs <> [] -> Disjoint _ (name_in_fundefs B) Code) ->
      Disjoint _ (FromList (rec_fields rs)) (FromList (rec_names rs)) ->
      FromList E \subset occurs_free_fundefs B :|: name_in_fundefs B ->
      IH_exp k ->
      G k (occurs_free_fundefs B) rho1 rho2 ->
      term_util.binding_in_map (occurs_free_fundefs B) rho1 ->
      code_env (def_funs Bk Bk rho2 rho2) ->
      (forall f, name_in_fundefs Bk f -> V k (Vfun rho1 B f) (Vfun rho2 Bk f)) /\
      (forall f w c zs, rec_of rs f = Some (w, c, zs) ->
                        exists vs2, get_list zs (def_funs Bk Bk rho2 rho2) = Some vs2 /\
                                    V k (Vfun rho1 B f) (Vconstr w c vs2)).
    Proof.
      intros HB Hnd Hdn Hdfn HE. induction k as [k IHk] using lt_wf_rec.
      intros Hexp HG Hbim Hcode.
      destruct (trans_bundle_nodup _ _ _ _ _ _ _ _ HB Hnd) as [Hndr Hdkr].
      assert (Hnames : forall g, name_in_fundefs B g <-> name_in_fundefs Bk g \/ List.In g (rec_names rs))
        by (eapply trans_bundle_names; eauto).
      assert (Hlow : forall j, j < k ->
                (forall f, name_in_fundefs Bk f -> V j (Vfun rho1 B f) (Vfun rho2 Bk f)) /\
                (forall f w c zs, rec_of rs f = Some (w, c, zs) ->
                                  exists vs2, get_list zs (def_funs Bk Bk rho2 rho2) = Some vs2 /\
                                              V j (Vfun rho1 B f) (Vconstr w c vs2))).
      { intros j Hj. eapply IHk; eauto.
        - intros m ex e e' r1 r2 Hm. eapply Hexp. lia.
        - eapply (G_mono cenv VT); eauto. lia. }
      assert (Hwf1 : wf_env rho1) by apply HG.
      assert (Hwf2 : wf_env rho2) by apply HG.
      assert (Hwfd2 : wf_env (def_funs Bk Bk rho2 rho2)) by (eapply wf_env_def_funs; eauto).
      (* the records *)
      assert (Hrecs : forall f w c zs, rec_of rs f = Some (w, c, zs) ->
                        exists vs2, get_list zs (def_funs Bk Bk rho2 rho2) = Some vs2 /\
                                    V k (Vfun rho1 B f) (Vconstr w c vs2)).
      { intros f w c zs Hr.
        edestruct (trans_bundle_sel _ _ _ _ _ _ _ _ _ _ _ _ HB Hnd Hr) as
          (-> & xs & ys & lams & code & wc & args & Hfd & Hw & HLw & Hinc & HTc & Hcc & Hwc & HLwc & Hndx & Hdxy & Hcx & Hargs).
        assert (Hrs : rs <> []) by (destruct rs; simpl in Hr; congruence).
        specialize (Hdn Hrs).
        (* the fields: the environment of the bundle *)
        edestruct (get_list_pointwise (fun v1 v2 => forall j, j < k -> V j v1 v2) E
                     (def_funs B B rho1 rho1) (def_funs Bk Bk rho2 rho2)) as (vE & vs2 & Hg1 & Hg2 & Hall).
        { intros z Hz.
          assert (Hzr : ~ List.In z (rec_names rs)).
          { intros Hc. eapply Hdfn. constructor; [ eapply rec_of_fields; eassumption | eassumption ]. }
          destruct (name_in_fundefs_dec Bk z) as [Hk | Hk].
          - do 2 eexists. split; [ rewrite def_funs_eq; [ reflexivity | eapply (proj2 (Hnames z)); now left ] |].
            split; [ rewrite def_funs_eq; [ reflexivity | eassumption ] |].
            intros j Hj. eapply (proj1 (Hlow j Hj)). eassumption.
          - assert (HnB : ~ name_in_fundefs B z) by (intros Hc; apply Hnames in Hc; tauto).
            assert (Hfz : occurs_free_fundefs B z) by (destruct (HE z Hz); [ eassumption | contradiction ]).
            edestruct (Hbim z) as [v1 Hv1]; [ exact Hfz |].
            edestruct (G_var_rel cenv VT P_ge k _ rho1 rho2 z HG) as (v2 & Hv2 & Hv); [ exact Hfz | eassumption |].
            exists v1, v2. rewrite !def_funs_neq; eauto. split; [ eassumption | split; [ eassumption |] ].
            intros j Hj. eapply (V_mono cenv VT); [ eassumption | lia ]. }
        (* the extra arguments of the code function *)
        assert (Hargs' : exists vys avs,
                   get_list ys (def_funs B B rho1 rho1) = Some vys /\ arg_vals vs2 args = Some avs /\
                   Forall2 (fun v1 v2 => forall j, j < k -> V j v1 v2) vys avs).
        { clear Hfd Hdxy HTc Hcx. induction Hargs as [| a y args ys Ha Hargs IH]; simpl.
          - do 2 eexists. split; [ reflexivity | split; [ reflexivity | constructor ] ].
          - destruct IH as (vys & avs & Hgy & Hav & Hvs). destruct a as [i | w' c']; simpl in Ha.
            + pose proof (get_list_nth_error E vE _ i y Hg1 Ha) as Hy1.
              assert (Hlen1 : length vE = length E) by (symmetry; eapply get_list_length_eq; eassumption).
              destruct (nth_error vE i) as [v1 |] eqn:Hv1.
              2:{ exfalso. eapply nth_error_None in Hv1. rewrite Hlen1 in Hv1.
                  assert (Hi : i < length E) by (eapply nth_error_Some; congruence). lia. }
              edestruct (Forall2_nth_error_l (fun v1 v2 => forall j, j < k -> V j v1 v2) vE vs2 i v1 Hall Hv1)
                as (v2 & Hv2 & Hv12).
              rewrite Hy1, Hgy, Hav, Hv2.
              do 2 eexists. split; [ reflexivity | split; [ reflexivity |] ]. constructor; eauto.
            + assert (Hry : rec_of rs y = Some (w', c', E)) by (eapply In_rec_of; eassumption).
              assert (HyB : name_in_fundefs B y) by (eapply (proj2 (Hnames y)); right; eapply rec_of_In; eassumption).
              rewrite def_funs_eq; [| exact HyB ]. rewrite Hgy, Hav.
              do 2 eexists. split; [ reflexivity | split; [ reflexivity |] ]. constructor; [| exact Hvs ].
              intros j Hj. edestruct (proj2 (Hlow j Hj) y w' c' E Hry) as (vs' & Hg' & Hv').
              rewrite Hg2 in Hg'. inv Hg'. exact Hv'. }
        destruct Hargs' as (vys & avs & Hgy & Hav & Hvys).
        assert (Hcfv : occurs_free_fundefs B code).
        { eapply occurs_free_in_fun in Hfd. edestruct (Hfd code) as [z' Hz' | z' Hz'].
          - eapply occurs_free_Eapp. now right.
          - contradiction.
          - destruct Hz' as [z' Hz' | z' Hz']; [| exact Hz' ].
            exfalso. eapply Hdn. constructor; eassumption. }
        assert (HcB : ~ name_in_fundefs B code) by (intros Hc; eapply Hdn; constructor; eassumption).
        assert (HcBk : ~ name_in_fundefs Bk code) by (intros Hc; eapply HcB, Hnames; now left).
        edestruct (Hbim code Hcfv) as [vcode Hvc1].
        edestruct (G_var_rel cenv VT P_ge k _ rho1 rho2 code HG Hcfv vcode Hvc1) as (vc2 & Hvc2 & Hvc).
        assert (Hvc2' : vc2 = Vfun rtop Btop' code).
        { specialize (Hcode code Hcc). rewrite def_funs_neq in Hcode; [ congruence | eassumption ]. }
        subst vc2.
        exists vs2. split; [ eassumption |].
        assert (Hlen : length vs2 = length E) by (symmetry; eapply get_list_length_eq; eassumption).
        eapply (V_Vfun_sel cenv sel (VT_dfn rtop) P_ge); [ eassumption | | eapply not_exposed_record; eassumption
                                                         | eassumption | eassumption | eapply sel_L_Some; eassumption |].
        - constructor; [ congruence |]. eapply wf_env_get_list; eassumption.
        - unfold VT_dfn. exists xs, ys, lams, code, wc, args, vcode, vys, avs.
          split; [ eassumption |]. split; [ eassumption |]. split; [ eassumption |].
          split; [ rewrite Hlen; eassumption |].
          do 5 (split; [ eassumption |]).
          split; [ rewrite def_funs_neq; eassumption |].
          split; [ eassumption |]. split; [ eassumption |].
          intros j Hj. split; [ eapply (V_mono cenv VT); [ eassumption | lia ] |].
          eapply Forall2_monotonic; [| eassumption ]. intros v1 v2 Hv12. eapply Hv12. eassumption. }
      split; [| exact Hrecs ].
      (* the kept functions *)
      intros f Hfk.
      edestruct name_in_fundefs_find_def as (w & xs & e2 & Hfd2); [ eassumption |].
      edestruct (trans_bundle_keep _ _ _ _ _ _ _ _ _ _ _ _ HB Hnd Hfd2) as (e & e' & Hfd1 & -> & Htr & Hkw & Hdx).
      eapply (V_Vfun_keeps cenv sel (VT_dfn rtop) P_ge); eauto.
      eapply (V_fun_def cenv VT P_ge); eauto.
      intros j vs1 vs2 rho1' rho2' Hj Hexpv Hvs Hs1 Hs2.
      eapply E_bind_recs_r; [ eapply P_ge_target_steps | eapply trans_bundle_internal; eassumption | |].
      2:{ eapply recs_env_exists; [ eassumption | eassumption |].
          intros g w' c' zs' Hr. edestruct (Hrecs g w' c' zs' Hr) as (vs' & Hg' & _).
          exists vs'. erewrite get_list_set_lists_Disjoint; [ eassumption | | eassumption ].
          eapply Disjoint_Included_r; [| exact Hdx ]. intros z Hz. left. right.
          eapply rec_of_fields; eassumption. }
      intros rho2'' Hre.
      assert (Hfve : occurs_free e \subset FromList xs :|: (name_in_fundefs B :|: occurs_free_fundefs B))
        by (eapply occurs_free_in_fun; eassumption).
      assert (Hwf1' : wf_env rho1').
      { eapply (wf_env_set_lists (def_funs B B rho1 rho1) rho1' xs vs1); [ eapply wf_env_def_funs; eauto | | exact Hs1 ].
        eapply (Forall2_V_wf_l cenv VT); eauto. }
      assert (Hwf2' : wf_env rho2').
      { eapply (wf_env_set_lists (def_funs Bk Bk rho2 rho2) rho2' xs vs2); [ eassumption | | exact Hs2 ].
        eapply (Forall2_V_wf_r cenv VT); eauto. }
      eapply Hexp; [ eassumption | eassumption |].
      split; [ split; [ exact Hwf1' | split ] | split ].
      - eapply recs_env_wf; eauto. eapply trans_bundle_internal; eassumption.
      - intros y Hy v1 Hget1. eapply Hfve in Hy.
        destruct (in_dec peq y xs) as [Hxs | Hxs].
        + edestruct (set_lists_Forall2_get (V j) xs vs1 vs2) as (v1' & v2' & Hg1 & Hg2 & Hr12);
            [ eassumption | eassumption | eassumption | eassumption |].
          rewrite Hg1 in Hget1. inv Hget1. eexists. split; [| eassumption ].
          erewrite recs_env_get_neq; [ eassumption | eassumption |].
          intros Hc. eapply Hdx. constructor; [ eassumption | now right ].
        + rewrite <- (set_lists_not_In xs vs1 _ rho1' y Hs1 Hxs) in Hget1.
          destruct (in_dec peq y (rec_names rs)) as [Hyr | Hyr].
          * (* a wrapper sibling: closure vs record *)
            edestruct (rec_names_rec_of rs y Hyr) as (w' & c' & zs' & Hr').
            rewrite def_funs_eq in Hget1; [| eapply (proj2 (Hnames y)); now right ]. inv Hget1.
            edestruct (recs_env_get_eq rs rho2' rho2'' y) as (vs' & Hg' & Hy2); eauto.
            edestruct (proj2 (Hlow j Hj) y w' c' zs' Hr') as (vs'' & Hg'' & Hv'').
            rewrite (get_list_set_lists_Disjoint xs zs' vs2 (def_funs Bk Bk rho2 rho2) rho2') in Hg'; [| | exact Hs2 ].
            -- rewrite Hg' in Hg''. inv Hg''. eexists; split; eauto.
            -- eapply Disjoint_Included_r; [| exact Hdx ]. intros z Hz. left. right.
               eapply rec_of_fields; eassumption.
          * erewrite recs_env_get_neq; [| eassumption | eassumption ].
            rewrite <- (set_lists_not_In xs vs2 _ rho2' y Hs2 Hxs).
            destruct (name_in_fundefs_dec Bk y) as [HyBk | HyBk].
            -- rewrite def_funs_eq in Hget1; [| eapply (proj2 (Hnames y)); now left ]. inv Hget1.
               rewrite def_funs_eq; [| eassumption ]. eexists; split; [ reflexivity |].
               eapply (proj1 (Hlow j Hj)). eassumption.
            -- assert (HyB : ~ name_in_fundefs B y) by (intros Hc; apply Hnames in Hc; tauto).
               rewrite def_funs_neq in Hget1; [| eassumption ]. rewrite def_funs_neq; [| eassumption ].
               destruct Hy as [y Hy | y Hy]; [ contradiction |].
               destruct Hy as [y Hy | y Hy]; [ contradiction |].
               edestruct (G_var_rel cenv VT P_ge k _ rho1 rho2 y HG Hy v1 Hget1) as (v2 & Hg2 & Hv).
               eexists; split; [ eassumption |]. eapply (V_mono cenv VT); [ eassumption | lia ].
      - eapply bim_set_lists_def_funs; eassumption.
      - intros c Hc. erewrite recs_env_get_neq; [| eassumption |].
        + rewrite <- (set_lists_not_In xs vs2 _ rho2' c Hs2); [ eapply Hcode; eassumption |].
          intros Hin. eapply Hdx. constructor; [ eassumption | left; left; eassumption ].
        + intros Hin. destruct rs as [| r rs']; [ inv Hin |].
          eapply (Hdn ltac:(congruence)). constructor; [| eassumption ].
          eapply (proj2 (Hnames c)). now right.
    Qed.

    Lemma E_fun_dfn ex k rho1 rho2 Ev B Bk rs e e' :
      trans_bundle Ev rs B Bk rs ->
      NoDup (fnames B) ->
      (rs <> [] -> Disjoint _ (name_in_fundefs B) Code) ->
      Disjoint _ (FromList (rec_fields rs)) (FromList (rec_names rs)) ->
      FromList Ev \subset occurs_free_fundefs B :|: name_in_fundefs B ->
      IH_exp k ->
      (forall rho1' rho2', Gd k (occurs_free e) rho1' rho2' -> E P_ge ex k (e, rho1') (e', rho2')) ->
      G k (occurs_free (Efun B e)) rho1 rho2 ->
      term_util.binding_in_map (occurs_free (Efun B e)) rho1 ->
      code_env (def_funs Bk Bk rho2 rho2) ->
      E P_ge ex k (Efun B e, rho1) (fun_recs Bk rs e', rho2).
    Proof.
      intros HB Hnd Hdn Hdfn HE Hexp Hcont HG Hbim Hcode.
      destruct (trans_bundle_nodup _ _ _ _ _ _ _ _ HB Hnd) as [Hndr Hdkr].
      assert (Hnames : forall g, name_in_fundefs B g <-> name_in_fundefs Bk g \/ List.In g (rec_names rs))
        by (eapply trans_bundle_names; eauto).
      edestruct (V_bundle k rho1 rho2 Ev B Bk rs) as [Hkeep Hrecs]; eauto.
      { eapply (G_antimon cenv VT); [ eassumption | eapply occurs_free_fundefs_Efun_Included ]. }
      { intros x Hx. eapply Hbim. eapply occurs_free_fundefs_Efun_Included. eassumption. }
      assert (Hint : recs_internal rs) by (eapply trans_bundle_internal; eassumption).
      edestruct (recs_env_exists rs (def_funs Bk Bk rho2 rho2)) as [rho2r Hre]; [ eassumption | eassumption | |].
      { intros g w c zs Hr. edestruct Hrecs as (vs & Hg & _); eauto. }
      assert (Hwf2 : wf_env rho2) by apply HG.
      assert (Hgd : Gd k (occurs_free e) (def_funs B B rho1 rho1) rho2r).
      { split; [ split; [| split ] | split ].
        - eapply wf_env_def_funs; apply HG.
        - eapply recs_env_wf; [ eassumption | eapply wf_env_def_funs; eauto | eassumption ].
        - intros x Hx v1 Hget1.
          destruct (in_dec peq x (rec_names rs)) as [Hxr | Hxr].
          + edestruct (rec_names_rec_of rs x Hxr) as (w & c & zs & Hr).
            rewrite def_funs_eq in Hget1; [| eapply (proj2 (Hnames x)); now right ]. inv Hget1.
            edestruct (recs_env_get_eq rs (def_funs Bk Bk rho2 rho2) rho2r x) as (vs & Hg & Hx2); eauto.
            edestruct (Hrecs x w c zs Hr) as (vs' & Hg' & Hv). rewrite Hg in Hg'. inv Hg'.
            eexists; split; eauto.
          + erewrite recs_env_get_neq; [| eassumption | eassumption ].
            destruct (name_in_fundefs_dec Bk x) as [HxBk | HxBk].
            * rewrite def_funs_eq in Hget1; [| eapply (proj2 (Hnames x)); now left ]. inv Hget1.
              rewrite def_funs_eq; [| eassumption ]. eexists; split; [ reflexivity | eauto ].
            * assert (HxB : ~ name_in_fundefs B x) by (intros Hc; apply Hnames in Hc; tauto).
              rewrite def_funs_neq in Hget1; [| eassumption ]. rewrite def_funs_neq; [| eassumption ].
              eapply (G_var_rel cenv VT P_ge k _ rho1 rho2 x HG); [| eassumption ].
              eapply occurs_free_Efun. right. constructor; eauto.
        - intros x Hx. destruct (name_in_fundefs_dec B x) as [Hn | Hn].
          + rewrite def_funs_eq; eauto.
          + rewrite def_funs_neq; eauto. eapply Hbim. eapply occurs_free_Efun. right. constructor; eauto.
        - intros c Hc. erewrite recs_env_get_neq; [ eapply Hcode; eassumption | eassumption |].
          intros Hin. destruct rs as [| r rs']; [ inv Hin |].
          eapply (Hdn ltac:(congruence)). constructor; [| eassumption ].
          eapply (proj2 (Hnames c)). now right. }
      intros r1 cin cout Hleq Hs. inv Hs.
      - exists OOT, cin, <0>. split; [ constructor; eapply lt_one_w; eassumption |].
        split; [ simpl; eapply ge_refl | exact I ].
      - inv H.
        edestruct (Hcont _ _ Hgd) as (r2 & cin' & cout' & Hs2 & Hpost & HR); [| eassumption |].
        { rewrite to_nat_add in Hleq. lia. }
        edestruct (bstep_bind_recs cenv ex e' cin' r2 cout' rs _ rho2r Hre Hint Hs2)
          as (cin'' & cout'' & Hs3 & Hge & Hge').
        assert (HR' : R cenv VT P_ge (k - to_nat (cin0 <+> one_w (Efun B e))) r1 r2).
        { eapply (R_mono cenv VT); eauto. rewrite to_nat_add. lia. }
        simpl in Hpost.
        assert (Hgen : exists cin4 cout4,
                   bstep_fuel cenv ex rho2 (Efun Bk (bind_recs rs e')) cin4 r2 cout4 /\
                   P_ge (Efun B e, rho1, cin0 <+> one_w (Efun B e), cout0 <+> one_w (Efun B e))
                        (Efun Bk (bind_recs rs e'), rho2, cin4, cout4)).
        { do 2 eexists. split.
          - econstructor 2; [ econstructor; eassumption | eapply bstep_fuel_ex_exposed; eassumption ].
          - simpl. rewrite (one_w_eq (Efun Bk _) (Efun B e)).
            eapply ge_add; [ eapply ge_trans; eassumption | eapply ge_refl ]. }
        destruct Bk as [ f w xs eb Bk' |]; [| destruct rs as [| r rs']];
          try (destruct Hgen as (cin4 & cout4 & Hs4 & Hp4); exists r2, cin4, cout4; split; [ exact Hs4 | split; [ exact Hp4 | exact HR' ] ]).
        exists r2, cin'', cout''. split; [ exact Hs3 | split; [| exact HR' ] ].
        destruct Hge as [ Hc | Hge ]; [ congruence |]. simpl.
        eapply ge_trans; [ exact Hge |]. rewrite (one_w_eq (Ehalt 1%positive) (Efun B e)).
        eapply ge_add; [ eassumption | eapply ge_refl ].
    Qed.

    (** ** Fundamental property *)

    Lemma dfn_fundamental k :
      forall ex e e' rho1 rho2, trans e e' -> Gd k (occurs_free e) rho1 rho2 -> E P_ge ex k (e, rho1) (e', rho2).
    Proof.
      induction k as [k IH] using lt_wf_rec.
      assert (IH' : IH_exp k) by (intros m ex e e' r1 r2 Hm; eapply IH; eauto).
      intros ex e e' rho1 rho2 Htr. revert ex rho1 rho2.
      induction Htr; intros ex rho1 rho2 Hgd; pose proof Hgd as (HG & Hbind & Hcode);
        pose proof (P_ge_properties cenv) as [Hcon Hproj Hfun Hchd Hctl Happ Hlet HletO HOOT Hbase HGP].
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
      - (* Eletapp, kept *)
        eapply (E_letapp_compat cenv VT); eauto.
        + eapply (var_rel_keeps_fun cenv sel (VT_dfn rtop) P_ge); eauto. eapply (G_var_rel cenv VT); eauto. fv_mem.
        + eapply (G_Forall2_var_rel cenv VT); eauto. normalize_occurs_free. sets.
        + intros m v1 v2 Hlt _ Hv. eapply IH; eauto. eapply Gd_set; eauto.
          eapply Gd_antimon; [ eapply Gd_mono; [ eassumption | lia ] |]. normalize_occurs_free. sets.
      - (* Eletapp, duplicated continuation *)
        eapply E_letapp_dfn; eauto.
      - (* Eletapp, join point *)
        eapply E_letapp_join_dfn; eauto.
      - (* Eapp, kept *)
        eapply (E_app_compat cenv VT); eauto.
        + eapply (var_rel_keeps_fun cenv sel (VT_dfn rtop) P_ge); eauto. eapply (G_var_rel cenv VT); eauto. fv_mem.
        + eapply (G_Forall2_var_rel cenv VT); eauto. normalize_occurs_free. sets.
      - (* Eapp, defunctionalized *)
        eapply E_app_dfn; eauto.
      - (* Efun *)
        eapply E_fun_dfn; eauto.
        intros c Hc. rewrite def_funs_neq; [ eauto |].
        intros Hn. match goal with [ Hd : Disjoint _ (name_in_fundefs B) Code |- _ ] => eapply Hd end.
        constructor; [ eapply trans_bundle_names_sub; eassumption | eassumption ].
      - (* Eprim_val *)
        eapply (E_stuck_compat cenv VT); eauto. intros. eapply Eprim_val_stuck.
      - (* Eprim *)
        eapply (E_stuck_compat cenv VT); eauto. intros. eapply Eprim_stuck.
      - (* Ehalt *)
        eapply (E_halt_compat cenv VT); eauto. eapply (G_var_rel cenv VT); eauto. fv_mem.
    Qed.

  End WithTop.

  Lemma fun_recs_nil Bk e : fun_recs Bk [] e = Efun Bk e.
  Proof. destruct Bk; reflexivity. Qed.

  (** ** Top level *)

  Theorem dfn_correct e0 e0' :
    trans_bundle [] [] Btop Btop' [] -> NoDup (fnames Btop) -> trans e0 e0' ->
    E_web cenv P_ge P_ge (Efun Btop e0) (Efun Btop' e0').
  Proof.
    intros HB Hnd Htr k rho1 rho2 Htop Hb.
    assert (Hwf2 : wf_env rho2) by apply Htop.
    eapply (E_exposed_indep cenv (VT_sel cenv sel (VT_dfn rho2)) VT_web).
    rewrite <- (fun_recs_nil Btop' e0').
    pose proof (G_top_exposed_indep cenv VT_web (VT_sel cenv sel (VT_dfn rho2)) P_ge k _ rho1 rho2 Htop) as [HG _].
    eapply (E_fun_dfn rho2); eauto.
    - intros Hc; congruence.
    - constructor. intros z Hz. inv Hz. inv H.
    - intros z Hz. inv Hz.
    - intros m ex e e' r1 r2 Hm. eapply dfn_fundamental; eauto.
    - intros rho1' rho2'. eapply dfn_fundamental; eauto.
    - intros c Hc. rewrite def_funs_eq; [ reflexivity |].
      eapply (proj1 (trans_bundle_names _ _ _ _ _ _ _ _ HB c)) in Hc. destruct Hc as [Hc | Hc]; [ exact Hc | inv Hc ].
  Qed.

End DefuncRel.

(** * Top level *)

Section DefuncTop.

  Variable (cenv : term.ctor_env).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Variables (L : WM.t (list ctor_tag)) (T : ctab) (Btop : fundefs).

  Hypothesis HL :
    forall w lams, WM.get w L = Some lams ->
                   exists it, Forall (fun c => exists info, M.get c cenv = Some info /\
                                                            term.ctor_ind_tag info = it) lams.
  Hypothesis HT : forall w c code wc n args, T w c = Some (code, wc, n, args) -> Code Btop code.

  (** Defunctionalization is in the λweb relation. *)
  Theorem dfn_correct_top e et :
    trans_top L T Btop e et -> E_web cenv (P_ge : @exposed.PostT fuel trace) P_ge e et.
  Proof.
    intros (e0 & Btop' & e0' & -> & -> & HB & Hnd & Htr).
    eapply (dfn_correct cenv L T Btop Btop' HL HT); eauto.
  Qed.

  (** Behavioral refinement of closed programs, including divergence
      preservation (the target takes at least as many steps). *)
  Corollary dfn_refines e et :
    closed_exp e -> trans_top L T Btop e et -> refines cenv value_ref e et.
  Proof.
    intros Hc Htr.
    eapply (E_web_refines cenv (P_ge : @exposed.PostT fuel trace) P_ge P_ge_upper_bound); eauto.
    eapply dfn_correct_top; eauto.
  Qed.

End DefuncTop.

(** * Free variables

    The output of defunctionalization only refers to the free variables of
    the input: code functions are referred to by name, but they are bound at
    the top of the program.  This is what [web_exp_n] needs to compose the
    pass with the others. *)

Combined Scheme trans_mutind from trans_mut, trans_bundle_mut.

(** The free variables of the bodies of a bundle, before removing its names *)
Fixpoint bfv (B : fundefs) : Ensemble var :=
  match B with
  | Fcons f w xs e B => (occurs_free e \\ FromList xs) :|: bfv B
  | Fnil => Empty_set var
  end.

Lemma occurs_free_fundefs_iff B z :
  occurs_free_fundefs B z <-> ~ name_in_fundefs B z /\ bfv B z.
Proof.
  induction B as [f w xs e B IH |]; simpl.
  - destruct (occurs_free_fundefs_Fcons f w xs e B) as [Hl Hr]. split.
    + intros Hz. eapply Hl in Hz. destruct Hz as [z Hz | z Hz]; inv Hz.
      * split; [ intros Hc; eapply H0; inv Hc; [ now left | now right; right ] |].
        left. constructor; [ eassumption | intros Hc; eapply H0; now right; left ].
      * eapply IH in H. destruct H as [Hn Hb]. split; [| now right ].
        intros Hc; inv Hc; [ eapply H0; eassumption | contradiction ].
    + intros [Hn Hb]. eapply Hr. inv Hb.
      * inv H. left. constructor; [ eassumption |].
        intros Hc; inv Hc; [ eapply Hn; now left |]. inv H.
        -- contradiction.
        -- eapply Hn; now right.
      * right. constructor; [ eapply IH; split; [ intros Hc; eapply Hn; now right | eassumption ] |].
        intros Hc; eapply Hn; now left.
  - destruct occurs_free_fundefs_Fnil as [Hl Hr]. split; intros H.
    + eapply Hl in H. inv H.
    + destruct H as [_ H]. inv H.
Qed.

Lemma occurs_free_Efun_iff B e z :
  occurs_free (Efun B e) z <-> ~ name_in_fundefs B z /\ (occurs_free e z \/ bfv B z).
Proof.
  destruct (occurs_free_Efun B e) as [Hl Hr]. split.
  - intros Hz. eapply Hl in Hz. destruct Hz as [z Hz | z Hz].
    + eapply occurs_free_fundefs_iff in Hz. destruct Hz. split; eauto.
    + inv Hz. split; eauto.
  - intros [Hn [Hz | Hz]]; eapply Hr.
    + right. constructor; eauto.
    + left. eapply occurs_free_fundefs_iff. eauto.
Qed.

Lemma occurs_free_bind_recs rs e z :
  occurs_free (bind_recs rs e) z ->
  (occurs_free e z /\ ~ List.In z (rec_names rs)) \/ List.In z (rec_fields rs).
Proof.
  induction rs as [| [[[f w] c] zs] rs IH]; simpl; [ intros; left; split; eauto |].
  intros Hz. eapply occurs_free_Econstr in Hz. unfold rec_fields in *; simpl.
  destruct Hz as [z Hz | z Hz].
  - right. eapply in_or_app. now left.
  - inv Hz. destruct (IH H) as [[Hz Hn] | Hz].
    + left. split; eauto. intros [Hc | Hc]; [ subst; eapply H0; constructor | contradiction ].
    + right. eapply in_or_app. now right.
Qed.

Lemma occurs_free_projs zs w c n g e z :
  occurs_free (projs zs w c n g e) z -> z = g \/ (occurs_free e z /\ ~ List.In z zs).
Proof.
  revert n. induction zs as [| y zs IH]; simpl; intros n Hz; [ right; split; eauto |].
  eapply occurs_free_Eproj in Hz. destruct Hz as [z Hz | z Hz]; [ inv Hz; now left |].
  inv Hz. destruct (IH _ H) as [Hg | [Hz Hn]]; [ now left |].
  right. split; eauto. intros [Hc | Hc]; [ subst; eapply H0; constructor | contradiction ].
Qed.

Fixpoint sib_vars (args : list arg) (ss : list var) : list var :=
  match args, ss with
  | ASib _ _ :: args, s :: ss => s :: sib_vars args ss
  | AEnv _ :: args, _ :: ss => sib_vars args ss
  | _, _ => []
  end.

Lemma arg_vars_sib zs args ss z : List.In z (arg_vars zs args ss) -> List.In z zs \/ List.In z (sib_vars args ss).
Proof.
  revert ss. induction args as [| [i | w c] args IH]; intros [| s ss] Hz; simpl in *; try contradiction.
  - destruct (nth_error zs i) as [z' |] eqn:Hz'; [ destruct Hz as [Hz | Hz] |].
    + subst. left. eapply nth_error_In. eassumption.
    + eauto.
    + eauto.
  - destruct Hz as [Hz | Hz]; [ subst; right; now left |].
    destruct (IH ss Hz); [ now left | right; now right ].
Qed.

Lemma occurs_free_arg_binds zs args ss e z :
  occurs_free (arg_binds zs args ss e) z -> List.In z zs \/ (occurs_free e z /\ ~ List.In z (sib_vars args ss)).
Proof.
  revert ss. induction args as [| [i | w c] args IH]; intros [| s ss] Hz; simpl in *; eauto.
  eapply occurs_free_Econstr in Hz. destruct Hz as [z Hz | z [Hz Hn]]; [ now left |].
  destruct (IH ss Hz) as [Hz' | [Hz' Hn']]; [ now left |].
  right. split; [ exact Hz' |]. intros [Hc | Hc]; [ subst; eapply Hn; constructor | contradiction ].
Qed.

Lemma occurs_free_dispatch g w alts call z :
  occurs_free (dispatch g w alts call) z ->
  z = g \/ exists c code wc zs args ss,
              List.In (c, code, wc, zs, args, ss) alts /\
              occurs_free (call code wc (arg_vars zs args ss)) z /\
              ~ List.In z zs /\ ~ List.In z (sib_vars args ss).
Proof.
  unfold dispatch. induction alts as [| [[[[[c code] wc] zs] args] ss] alts IH]; simpl; intros Hz.
  - eapply occurs_free_Ecase_nil in Hz. inv Hz. now left.
  - eapply occurs_free_Ecase_cons in Hz. destruct Hz as [z Hz | z Hz]; [ inv Hz; now left |].
    destruct Hz as [z Hz | z Hz].
    + destruct (occurs_free_projs _ _ _ _ _ _ _ Hz) as [Hg | [Hz' Hn]]; [ now left |].
      destruct (occurs_free_arg_binds _ _ _ _ _ Hz') as [Hc | [Hz'' Hns]]; [ contradiction |].
      right. do 6 eexists. split; [ now left | eauto ].
    + destruct (IH Hz) as [Hg | (c' & code' & wc' & zs' & args' & ss' & Hin & Hz' & Hn & Hns)]; [ now left |].
      right. do 6 eexists. split; [ now right | eauto ].
Qed.

Lemma arg_vars_bound zs args ss z :
  List.In z (arg_vars zs args ss) -> ~ List.In z zs -> ~ List.In z (sib_vars args ss) -> False.
Proof. intros Hz Hn Hns. destruct (arg_vars_sib _ _ _ _ Hz); contradiction. Qed.

Lemma occurs_free_fun_recs Bk rs e z :
  occurs_free (fun_recs Bk rs e) z ->
  ~ name_in_fundefs Bk z /\ (occurs_free (bind_recs rs e) z \/ bfv Bk z).
Proof.
  unfold fun_recs. destruct Bk; [| destruct rs ];
    try (intros Hz; eapply occurs_free_Efun_iff in Hz; exact Hz).
  intros Hz. split; [ intros Hc; inv Hc | now left ].
Qed.


Section DefuncFV.

  Variables (L : WM.t (list ctor_tag)) (T : ctab) (Btop : fundefs).

  (** The code functions of the lambda sets are among [Btop] *)
  Hypothesis (HT : forall w c code wc n args, T w c = Some (code, wc, n, args) -> Code Btop code).

  Local Notation Code := (Code Btop).

  Lemma alts_ok_code w alts avoid c code wc zs args ss :
    alts_ok L T Btop w alts avoid -> List.In (c, code, wc, zs, args, ss) alts -> Code code.
  Proof.
    intros [_ Hall] Hin. eapply Forall_forall in Hall; [| exact Hin ]. simpl in Hall.
    destruct Hall as [HTc _]. eapply HT; eassumption.
  Qed.

  Lemma trans_fv :
    (forall e e', trans L T Btop e e' ->
                  forall z, occurs_free e' z -> occurs_free e z \/ Code z) /\
    (forall E rs0 B Bk rs, trans_bundle L T Btop E rs0 B Bk rs ->
       (forall z, bfv Bk z ->
                  ((bfv B z \/ Code z) /\ ~ List.In z (rec_names rs0)) \/ List.In z (rec_fields rs0)) /\
       (forall z, List.In z (rec_fields rs) -> List.In z E) /\
       (forall z, name_in_fundefs B z <-> name_in_fundefs Bk z \/ List.In z (rec_names rs))).
  Proof.
    eapply trans_mutind.
    - (* Econstr *)
      intros x w t ys e e' Hx Ht IH z Hz.
      eapply occurs_free_Econstr in Hz. destruct Hz as [z Hz | z [Hz Hn]].
      + left. eapply occurs_free_Econstr. now left.
      + destruct (IH _ Hz) as [Hz' | Hz']; [| now right ].
        left. eapply occurs_free_Econstr. right. constructor; eauto.
    - (* Eproj *)
      intros x w t n y e e' Hx Ht IH z Hz.
      eapply occurs_free_Eproj in Hz. destruct Hz as [z Hz | z [Hz Hn]].
      + left. eapply occurs_free_Eproj. now left.
      + destruct (IH _ Hz) as [Hz' | Hz']; [| now right ].
        left. eapply occurs_free_Eproj. right. constructor; eauto.
    - (* Ecase nil *) intros x w z Hz. now left.
    - (* Ecase cons *)
      intros x w c e e' cl cl' Ht IH Htc IHc z Hz.
      eapply occurs_free_Ecase_cons in Hz. destruct Hz as [z Hz | z [? Hz | ? Hz]].
      + left. eapply occurs_free_Ecase_cons. now left.
      + destruct (IH _ Hz) as [Hz' | Hz']; [| now right ].
        left. eapply occurs_free_Ecase_cons. right. now left.
      + destruct (IHc _ Hz) as [Hz' | Hz']; [| now right ].
        left. eapply occurs_free_Ecase_cons. right. now right.
    - (* Eletapp, kept *)
      intros x f w ys e e' Hk Hx Ht IH z Hz.
      eapply occurs_free_Eletapp in Hz. destruct Hz as [z Hz | z [Hz Hn]].
      + left. eapply occurs_free_Eletapp. now left.
      + destruct (IH _ Hz) as [Hz' | Hz']; [| now right ].
        left. eapply occurs_free_Eletapp. right. constructor; eauto.
    - (* Eletapp, continuation duplicated *)
      intros x f w ys e e' alts Hw Hx Ha Ht IH z Hz.
      eapply occurs_free_dispatch in Hz.
      destruct Hz as [Hz | (c & code & wc & zs & args & ss & Hin & Hz & Hn & Hns)].
      + subst. left. eapply occurs_free_Eletapp. left. now left.
      + eapply occurs_free_Eletapp in Hz. destruct Hz as [? [? Hz | ? Hz] | ? [Hz Hnx]].
        * inv Hz. right. eapply alts_ok_code; eauto.
        * eapply in_app_or in Hz. destruct Hz as [Hz | Hz]; [| exfalso; eapply arg_vars_bound; eassumption ].
          left. eapply occurs_free_Eletapp. left. now right.
        * destruct (IH _ Hz) as [Hz' | Hz']; [| now right ].
          left. eapply occurs_free_Eletapp. right. constructor; eauto.
    - (* Eletapp, join point *)
      intros x f w ys e e' alts j wj Hw Hx Hwj Hj Hjx Hjf Hjys Hje Ha Ht IH z Hz.
      eapply occurs_free_Efun_iff in Hz. destruct Hz as [Hnj [Hz | Hz]].
      + eapply occurs_free_dispatch in Hz.
        destruct Hz as [Hz | (c & code & wc & zs & args & ss & Hin & Hz & Hn & Hns)].
        * subst. left. eapply occurs_free_Eletapp. left. now left.
        * eapply occurs_free_Eletapp in Hz. destruct Hz as [? [? Hz | ? Hz] | ? [Hz Hnx]].
          -- inv Hz. right. eapply alts_ok_code; eauto.
          -- eapply in_app_or in Hz. destruct Hz as [Hz | Hz]; [| exfalso; eapply arg_vars_bound; eassumption ].
             left. eapply occurs_free_Eletapp. left. now right.
          -- exfalso. eapply occurs_free_Eapp in Hz. destruct Hz as [z Hz | z Hz].
             ++ destruct Hz as [Hz | []]. subst. eapply Hnx. constructor.
             ++ inv Hz. eapply Hnj. now left.
      + simpl in Hz. destruct Hz as [? [Hz Hnx] | ? Hz]; [| inv Hz ].
        destruct (IH _ Hz) as [Hz' | Hz']; [| now right ].
        left. eapply occurs_free_Eletapp. right. constructor; eauto.
        intros Hc; inv Hc. eapply Hnx. now left.
    - (* Eapp, kept *) intros f w ys Hk z Hz. now left.
    - (* Eapp, dispatched *)
      intros f w ys alts Hw Ha z Hz.
      eapply occurs_free_dispatch in Hz.
      destruct Hz as [Hz | (c & code & wc & zs & args & ss & Hin & Hz & Hn & Hns)].
      + subst. left. eapply occurs_free_Eapp. now right.
      + eapply occurs_free_Eapp in Hz. destruct Hz as [z Hz | z Hz].
        * eapply in_app_or in Hz. destruct Hz as [Hz | Hz]; [| exfalso; eapply arg_vars_bound; eassumption ].
          left. eapply occurs_free_Eapp. now left.
        * inv Hz. right. eapply alts_ok_code; eauto.
    - (* Efun *)
      intros Ev B Bk rs e e' Hb IHb Hnd Hdc Hdr HE Ht IH z Hz.
      destruct IHb as (Hbk & Hfields & Hnames).
      eapply occurs_free_fun_recs in Hz. destruct Hz as [Hnk [Hz | Hz]].
      + eapply occurs_free_bind_recs in Hz. destruct Hz as [[Hz Hnr] | Hz].
        * destruct (IH _ Hz) as [Hz' | Hz']; [| now right ].
          left. eapply occurs_free_Efun_iff. split; [| now left ].
          intros Hc. eapply Hnames in Hc. destruct Hc; contradiction.
        * left. eapply occurs_free_Efun_iff.
          destruct (HE z (Hfields z ltac:(eassumption))) as [? Hof | ? Hnm].
          -- eapply occurs_free_fundefs_iff in Hof. destruct Hof as [Hn' Hb'']. split; [ exact Hn' | now right ].
          -- exfalso. eapply Hnames in Hnm. destruct Hnm as [Hc | Hc]; [ contradiction |].
             eapply Hdr; constructor; eassumption.
      + destruct (Hbk _ Hz) as [[[Hb' | Hb'] Hnr] | Hb']; [| now right |].
        * left. eapply occurs_free_Efun_iff. split; [| now right ].
          intros Hc. eapply Hnames in Hc. destruct Hc; contradiction.
        * left. eapply occurs_free_Efun_iff.
          destruct (HE z (Hfields z ltac:(eassumption))) as [? Hof | ? Hnm].
          -- eapply occurs_free_fundefs_iff in Hof. destruct Hof as [Hn' Hb'']. split; [ exact Hn' | now right ].
          -- exfalso. eapply Hnames in Hnm. destruct Hnm as [Hc | Hc]; [ contradiction |].
             eapply Hdr; constructor; eassumption.
    - (* Eprim_val *)
      intros x p e e' Hx Ht IH z Hz.
      eapply (proj1 (occurs_free_Eprim_val _ _ _)) in Hz. destruct Hz as [Hz Hn].
      destruct (IH _ Hz) as [Hz' | Hz']; [| now right ].
      left. eapply (proj2 (occurs_free_Eprim_val _ _ _)). constructor; eauto.
    - (* Eprim *)
      intros x p ys e e' Hx Ht IH z Hz.
      eapply (proj1 (occurs_free_Eprim _ _ _ _)) in Hz. destruct Hz as [z Hz | z [Hz Hn]].
      + left. eapply (proj2 (occurs_free_Eprim _ _ _ _)). now left.
      + destruct (IH _ Hz) as [Hz' | Hz']; [| now right ].
        left. eapply (proj2 (occurs_free_Eprim _ _ _ _)). right. constructor; eauto.
    - intros x z Hz. now left.
    - (* TB_nil *)
      intros E rs0. split; [| split ]; simpl.
      + intros z Hz. inv Hz.
      + intros z [].
      + intros z. split; intros H; [ inv H | destruct H as [H | []]; inv H ].
    - (* TB_keep *)
      intros E rs0 f w xs e e' B Bk rs Hk Hd Ht IH Hb IHb.
      destruct IHb as (Hbk & Hfields & Hnames). split; [| split ].
      + intros z Hz. simpl in Hz. destruct Hz as [? [Hz Hnx] | ? Hz].
        * eapply occurs_free_bind_recs in Hz. destruct Hz as [[Hz Hnr] | Hz]; [| now right ].
          left. split; [| eassumption ].
          destruct (IH _ Hz) as [Hz' | Hz']; [| now right ].
          left. left. constructor; eassumption.
        * destruct (Hbk _ Hz) as [[[Hb' | Hb'] Hnr] | Hb']; [| | now right ].
          -- left. split; [ left; now right | eassumption ].
          -- left. split; [ now right | eassumption ].
      + intros z Hz. eapply Hfields. eassumption.
      + intros z. simpl. split.
        * intros Hz. destruct Hz as [z Hz | z Hz]; [ left; now left |].
          eapply Hnames in Hz. destruct Hz; [ left; now right | now right ].
        * intros [Hz | Hz]; [ destruct Hz as [z Hz | z Hz]; [ now left | right; eapply Hnames; now left ] |].
          right. eapply Hnames. now right.
    - (* TB_sel *)
      intros E rs0 f w xs zs B Bk rs lams c code wc args Hw HL Hin HTc Hc Hwc HLc Hnd Hdxz Hcx Hargs Hb IHb.
      destruct IHb as (Hbk & Hfields & Hnames). split; [| split ].
      + intros z Hz. destruct (Hbk _ Hz) as [[[Hb' | Hb'] Hnr] | Hb']; [| | now right ].
        * left. split; [ left; now right | eassumption ].
        * left. split; [ now right | eassumption ].
      + intros z Hz. unfold rec_fields in Hz. simpl in Hz. eapply in_app_or in Hz.
        destruct Hz as [Hz | Hz]; [ exact Hz | eapply Hfields; eassumption ].
      + intros z. simpl. split.
        * intros Hz. destruct Hz as [z Hz | z Hz]; [ inv Hz; right; now left |].
          eapply Hnames in Hz. destruct Hz; [ now left | right; now right ].
        * intros [Hz | [Hz | Hz]]; [ right; eapply Hnames; now left | subst; left; constructor |].
          right. eapply Hnames. now right.
  Qed.

  Lemma trans_top_preserves_fv e et : trans_top L T Btop e et -> preserves_fv e et.
  Proof.
    intros (e0 & Btop' & e0' & -> & -> & HB & Hnd & Htr) z Hz.
    destruct (proj2 trans_fv _ _ _ _ _ HB) as (Hbk & _ & Hnames).
    eapply occurs_free_Efun_iff in Hz. destruct Hz as [Hn Hz].
    assert (Hnc : ~ Code z).
    { intros Hc. eapply Hnames in Hc. destruct Hc as [Hc | []]. contradiction. }
    eapply occurs_free_Efun_iff. split; [ exact Hnc |].
    destruct Hz as [Hz | Hz].
    - destruct (proj1 trans_fv _ _ Htr _ Hz); [ now left | contradiction ].
    - destruct (Hbk _ Hz) as [[[Hb | Hb] _] | []]; [ now right | contradiction ].
  Qed.

End DefuncFV.
