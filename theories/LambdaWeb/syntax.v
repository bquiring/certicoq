(* λweb: λANF annotated with webs.

   λweb is CertiRocq's λANF in which every producer and consumer of a value
   carries a web identifier.  Following CertiRocq, functions and calls already
   carry a [fun_tag] that the semantics checks at every call; in λweb that tag
   is the web of the function (so the existing calling-convention tags of
   λANF are exactly a degenerate web annotation).  Constructors, projections
   and case analyses additionally carry a web.

   A fixed set of webs [Exposed] determines which values are visible to the
   outside world (imports, exports, and everything derived from them).  The
   semantics in [LambdaWeb.semantics] enforces that exposed functions are only
   called on exposed values and return exposed values, and that exposed
   constructors only package exposed values. *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics.
From CertiRocq.LambdaANF Require term identifiers.
From CertiRocq.Common Require AstCommon.
From CertiRocq.LambdaANF Require Export map_util.
From compcert.lib Require Export Maps.

Import ListNotations.

Module M := Maps.PTree.

Definition var := term.var.
Definition ctor_tag := term.ctor_tag.
Definition prim := term.prim.
Definition primitive_value := AstCommon.primitive_value.

(** * Webs

    A web is either exposed or internal.  The paper fixes a single set of
    exposed webs Δ shared by every correct compiler; here Δ is the set of
    webs built with [Exposed].  A function web plays the role of λANF's
    [fun_tag]: erasure maps a web to its index ([web_tag]), and exposed
    functions keep their λANF function tag ([Exposed t]). *)
Inductive web : Type :=
| Exposed : positive -> web
| Internal : positive -> web.

Definition webs := Ensemble web.

Definition exposedb (w : web) : bool :=
  match w with Exposed _ => true | Internal _ => false end.

Definition exposed_webs : webs := fun w => exposedb w = true.

Lemma exposedb_false w : exposedb w = false <-> ~ exposed_webs w.
Proof. unfold exposed_webs. destruct (exposedb w); split; congruence. Qed.

Definition web_eq_dec (w1 w2 : web) : {w1 = w2} + {w1 <> w2}.
Proof. decide equality; apply Pos.eq_dec. Defined.

Definition web_eqb (w1 w2 : web) : bool := if web_eq_dec w1 w2 then true else false.

Lemma web_eqb_eq w1 w2 : web_eqb w1 w2 = true <-> w1 = w2.
Proof. unfold web_eqb. destruct (web_eq_dec w1 w2); split; congruence. Qed.

Lemma web_eqb_refl w : web_eqb w w = true.
Proof. apply web_eqb_eq. reflexivity. Qed.

(** The λANF function tag of a web. *)
Definition web_tag (w : web) : term.fun_tag :=
  match w with Exposed t => t | Internal t => t end.

(** Maps indexed by webs *)
Definition web_index (w : web) : positive :=
  match w with Exposed p => xI p | Internal p => xO p end.

Definition web_of_index (p : positive) : web :=
  match p with xI p => Exposed p | xO p => Internal p | xH => Internal xH end.

Lemma web_of_index_index w : web_of_index (web_index w) = w.
Proof. destruct w; reflexivity. Qed.

Module WebIndexed <: INDEXED_TYPE.
  Definition t := web.
  Definition index := web_index.
  Lemma index_inj (x y : t) : index x = index y -> x = y.
  Proof. intros H. rewrite <- (web_of_index_index x), <- (web_of_index_index y). unfold index in H. congruence. Qed.
  Definition eq := web_eq_dec.
End WebIndexed.

Module WM := ITree(WebIndexed).

Lemma WM_gmap_filter1 {A B} (f : A -> option B) (m : WM.t A) w :
  WM.get w (M.map_filter1 f m) = match WM.get w m with Some a => f a | None => None end.
Proof. apply M.gmap_filter1. Qed.

(** The keys of a web map *)
Definition WM_elements {A} (m : WM.t A) : list (web * A) :=
  map (fun '(p, a) => (web_of_index p, a)) (M.elements m).

Lemma WM_elements_correct {A} (m : WM.t A) w a : WM.get w m = Some a -> List.In (w, a) (WM_elements m).
Proof.
  intros H. unfold WM_elements. eapply in_map_iff. exists (web_index w, a). split.
  - rewrite web_of_index_index. reflexivity.
  - eapply M.elements_correct. exact H.
Qed.

(** * Syntax *)

Inductive exp : Type :=
| Econstr : var -> web -> ctor_tag -> list var -> exp -> exp
| Ecase : var -> web -> list (ctor_tag * exp) -> exp
| Eproj : var -> web -> ctor_tag -> N -> var -> exp -> exp
| Eletapp : var -> var -> web -> list var -> exp -> exp
| Efun : fundefs -> exp -> exp
| Eapp : var -> web -> list var -> exp
| Eprim_val : var -> primitive_value -> exp -> exp
| Eprim : var -> prim -> list var -> exp -> exp
| Ehalt : var -> exp
with fundefs : Type :=
| Fcons : var -> web -> list var -> exp -> fundefs -> fundefs
| Fnil : fundefs.

Scheme exp_mut := Induction for exp Sort Prop
with fundefs_mut := Induction for fundefs Sort Prop.

Lemma exp_ind' :
  forall P : exp -> Type,
    (forall x w t ys e, P e -> P (Econstr x w t ys e)) ->
    (forall x w, P (Ecase x w nil)) ->
    (forall x w cl c e, P e -> P (Ecase x w cl) -> P (Ecase x w ((c, e) :: cl))) ->
    (forall x w t n y e, P e -> P (Eproj x w t n y e)) ->
    (forall x f w ys e, P e -> P (Eletapp x f w ys e)) ->
    (forall B e, P e -> P (Efun B e)) ->
    (forall f w ys, P (Eapp f w ys)) ->
    (forall x p e, P e -> P (Eprim_val x p e)) ->
    (forall x p ys e, P e -> P (Eprim x p ys e)) ->
    (forall x, P (Ehalt x)) ->
    forall e : exp, P e.
Proof.
  intros P H1 H2 H3 H4 H5 H6 H7 H8 H9 H10. fix exp_ind' 1.
  destruct e; try (now clear exp_ind'; eauto).
  - eapply H1. eapply exp_ind'.
  - induction l as [ | [c e] xs IHxs].
    + eapply H2.
    + eapply H3. apply exp_ind'. eauto.
  - eapply H4. eapply exp_ind'.
  - eapply H5. eapply exp_ind'.
  - eapply H6. eapply exp_ind'.
  - eapply H8. eapply exp_ind'.
  - eapply H9. eapply exp_ind'.
Qed.

(** Mutual induction, with the branches of a case analysis one at a time *)
Lemma exp_fundefs_ind (P : exp -> Prop) (Q : fundefs -> Prop) :
  (forall x w t ys e, P e -> P (Econstr x w t ys e)) ->
  (forall x w, P (Ecase x w nil)) ->
  (forall x w cl c e, P e -> P (Ecase x w cl) -> P (Ecase x w ((c, e) :: cl))) ->
  (forall x w t n y e, P e -> P (Eproj x w t n y e)) ->
  (forall x f w ys e, P e -> P (Eletapp x f w ys e)) ->
  (forall B e, Q B -> P e -> P (Efun B e)) ->
  (forall f w ys, P (Eapp f w ys)) ->
  (forall x p e, P e -> P (Eprim_val x p e)) ->
  (forall x p ys e, P e -> P (Eprim x p ys e)) ->
  (forall x, P (Ehalt x)) ->
  (forall f w xs e B, P e -> Q B -> Q (Fcons f w xs e B)) ->
  Q Fnil ->
  (forall e, P e) /\ (forall B, Q B).
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
  refine (conj
            (fix Fe (e : exp) : P e :=
               match e with
               | Econstr x w t ys k => H1 x w t ys k (Fe k)
               | Ecase x w cl =>
                   (fix Fcl (cl : list (ctor_tag * exp)) : P (Ecase x w cl) :=
                      match cl with
                      | [] => H2 x w
                      | (c, k) :: cl' => H3 x w cl' c k (Fe k) (Fcl cl')
                      end) cl
               | Eproj x w t n y k => H4 x w t n y k (Fe k)
               | Eletapp x f w ys k => H5 x f w ys k (Fe k)
               | Efun B k => H6 B k (Fb B) (Fe k)
               | Eapp f w ys => H7 f w ys
               | Eprim_val x p k => H8 x p k (Fe k)
               | Eprim x p ys k => H9 x p ys k (Fe k)
               | Ehalt x => H10 x
               end
             with Fb (B : fundefs) : Q B :=
               match B with
               | Fcons f w xs k B' => H11 f w xs k B' (Fe k) (Fb B')
               | Fnil => H12
               end
             for Fe)
            (fix Fe (e : exp) : P e :=
               match e with
               | Econstr x w t ys k => H1 x w t ys k (Fe k)
               | Ecase x w cl =>
                   (fix Fcl (cl : list (ctor_tag * exp)) : P (Ecase x w cl) :=
                      match cl with
                      | [] => H2 x w
                      | (c, k) :: cl' => H3 x w cl' c k (Fe k) (Fcl cl')
                      end) cl
               | Eproj x w t n y k => H4 x w t n y k (Fe k)
               | Eletapp x f w ys k => H5 x f w ys k (Fe k)
               | Efun B k => H6 B k (Fb B) (Fe k)
               | Eapp f w ys => H7 f w ys
               | Eprim_val x p k => H8 x p k (Fe k)
               | Eprim x p ys k => H9 x p ys k (Fe k)
               | Ehalt x => H10 x
               end
             with Fb (B : fundefs) : Q B :=
               match B with
               | Fcons f w xs k B' => H11 f w xs k B' (Fe k) (Fb B')
               | Fnil => H12
               end
             for Fb)).
Qed.

(** * Erasure to λANF

    Erasure forgets the webs of constructor forms; function webs become
    λANF function tags.  We use it to inherit the λANF notions that do not
    depend on webs (free and bound variables, resource units, ...). *)

Fixpoint erase (e : exp) : term.exp :=
  match e with
  | Econstr x w t ys e => term.Econstr x t ys (erase e)
  | Ecase x w cl =>
      term.Ecase x ((fix erase_branches (cl : list (ctor_tag * exp)) :=
                       match cl with
                       | [] => []
                       | (c, e) :: cl => (c, erase e) :: erase_branches cl
                       end) cl)
  | Eproj x w t n y e => term.Eproj x t n y (erase e)
  | Eletapp x f w ys e => term.Eletapp x f (web_tag w) ys (erase e)
  | Efun B e => term.Efun (erase_fundefs B) (erase e)
  | Eapp f w ys => term.Eapp f (web_tag w) ys
  | Eprim_val x p e => term.Eprim_val x p (erase e)
  | Eprim x p ys e => term.Eprim x p ys (erase e)
  | Ehalt x => term.Ehalt x
  end
with erase_fundefs (B : fundefs) : term.fundefs :=
  match B with
  | Fcons f w xs e B => term.Fcons f (web_tag w) xs (erase e) (erase_fundefs B)
  | Fnil => term.Fnil
  end.

Definition erase_branches (cl : list (ctor_tag * exp)) : list (ctor_tag * term.exp) :=
  map (fun '(c, e) => (c, erase e)) cl.

Lemma erase_Ecase x w cl : erase (Ecase x w cl) = term.Ecase x (erase_branches cl).
Proof.
  simpl. f_equal. induction cl as [| [c e] cl IH]; simpl; congruence.
Qed.

(** * Values *)

Inductive val : Type :=
| Vconstr : web -> ctor_tag -> list val -> val
| Vfun : M.t val -> fundefs -> var -> val
(* [Vfun ρ B f]: [B] is the bundle of mutually recursive functions that
   contains [f], and [ρ] is the environment at the definition site. *)
| Vprim : primitive_value -> val
| Vint : Z -> val.

Definition env := M.t val.

Lemma val_ind' :
  forall P : val -> Prop,
    (forall w t, P (Vconstr w t nil)) ->
    (forall w t v l, P v -> P (Vconstr w t l) -> P (Vconstr w t (v :: l))) ->
    (forall ρ B f, P (Vfun ρ B f)) ->
    (forall p, P (Vprim p)) ->
    (forall z, P (Vint z)) ->
    forall v : val, P v.
Proof.
  intros P H1 H2 H3 H4 H5.
  fix val_ind' 1.
  destruct v; try (now clear val_ind'; eauto).
  induction l as [ | x xs IHxs].
  - eapply H1.
  - eapply H2. apply val_ind'. eauto.
Qed.

Section ValInd.
  Context (P : val -> Prop)
          (Hconstr : forall w t vs, Forall P vs -> P (Vconstr w t vs))
          (Hfun : forall ρ B f, P (Vfun ρ B f))
          (Hprim : forall p, P (Vprim p))
          (Hint : forall z, P (Vint z)).

  Fixpoint val_ind_Forall (v : val) {struct v} : P v :=
    match v with
    | Vconstr w t vs =>
        Hconstr w t vs
          ((fix loop (vs : list val) : Forall P vs :=
              match vs with
              | [] => Forall_nil P
              | v :: vs => Forall_cons v (val_ind_Forall v) (loop vs)
              end) vs)
    | Vfun ρ B f => Hfun ρ B f
    | Vprim p => Hprim p
    | Vint z => Hint z
    end.
End ValInd.

Fixpoint def_funs (B0 B : fundefs) (ρ0 ρ : env) : env :=
  match B with
  | Fcons f w xs e B' => M.set f (Vfun ρ0 B0 f) (def_funs B0 B' ρ0 ρ)
  | Fnil => ρ
  end.

Fixpoint find_def (f : var) (B : fundefs) : option (web * list var * exp) :=
  match B with
  | Fcons f' w xs e B' => if M.elt_eq f f' then Some (w, xs, e) else find_def f B'
  | Fnil => None
  end.

Fixpoint name_in_fundefs (B : fundefs) : Ensemble var :=
  match B with
  | Fnil => Empty_set var
  | Fcons f _ _ _ B => Union var (Singleton var f) (name_in_fundefs B)
  end.

(** Webs of the functions defined in a bundle. *)
Definition fun_web (B : fundefs) (f : var) : option web :=
  match find_def f B with
  | Some (w, _, _) => Some w
  | None => None
  end.

(** Branch lookup for case analysis. *)
Inductive find_tag_nth : list (ctor_tag * exp) -> ctor_tag -> exp -> nat -> Prop :=
| find_tag_hd : forall c e l, find_tag_nth ((c, e) :: l) c e 1
| find_tag_lt : forall c e l c' e' n,
    find_tag_nth l c' e' n -> c <> c' -> find_tag_nth ((c, e) :: l) c' e' (n + 1).

Lemma find_tag_nth_deterministic l c e n e' n' :
  find_tag_nth l c e n -> find_tag_nth l c e' n' -> e = e' /\ n = n'.
Proof.
  intros H1. revert e' n'; induction H1; intros e1 n1 H2; inv H2; try congruence; eauto.
  - edestruct IHfind_tag_nth as [Heq1 Heq2]; eauto.
Qed.

(** * Exposed values

    A value is exposed if its web is exposed; an exposed constructor value
    must additionally contain only exposed values.  The environment of an
    exposed closure is opaque and may contain internal values.  Base values
    have no behavior a transformation could change, so they are exposed. *)

Fixpoint exposed_val (v : val) : Prop :=
  match v with
  | Vconstr w t vs =>
      exposedb w = true /\ fold_right (fun v acc => exposed_val v /\ acc) True vs
  | Vfun ρ B f =>
      match fun_web B f with
      | Some w => exposedb w = true
      | None => False
      end
  | Vprim _ | Vint _ => True
  end.

Lemma exposed_val_Vconstr w t vs :
  exposed_val (Vconstr w t vs) <-> exposedb w = true /\ Forall exposed_val vs.
Proof.
  simpl. split; intros [Hw Hvs]; split; auto.
  - induction vs; simpl in *; constructor; tauto.
  - induction Hvs; simpl; [ exact I | split; auto ].
Qed.

Lemma exposed_val_Vfun ρ B f :
  exposed_val (Vfun ρ B f) <->
  exists w xs e, find_def f B = Some (w, xs, e) /\ exposedb w = true.
Proof.
  simpl. unfold fun_web. destruct (find_def f B) as [[[w xs] e] |]; simpl.
  - split; intros H; eauto. destructAll. congruence.
  - split; intros H; [ contradiction | destructAll; congruence ].
Qed.

Global Opaque exposed_val.

(** * Results *)

Inductive res : Type :=
| OOT
| Res : val -> res.

Definition exposed_res (r : res) : Prop :=
  match r with
  | OOT => True
  | Res v => exposed_val v
  end.

(** * Well-formed values

    A value annotated with an exposed web must actually be exposed.  This is
    needed because an internal function may build an exposed-looking
    constructor out of internal values; the semantics forbids it. *)

Inductive wf_val : val -> Prop :=
| WF_Vconstr :
    forall w t vs,
      (exposedb w = true -> Forall exposed_val vs) ->
      Forall wf_val vs ->
      wf_val (Vconstr w t vs)
| WF_Vfun :
    forall ρ B f,
      wf_env ρ ->
      wf_val (Vfun ρ B f)
| WF_Vprim : forall p, wf_val (Vprim p)
| WF_Vint : forall z, wf_val (Vint z)
with wf_env : env -> Prop :=
| WF_env :
    forall ρ, (forall x v, M.get x ρ = Some v -> wf_val v) -> wf_env ρ.

Definition wf_res (r : res) : Prop :=
  match r with
  | OOT => True
  | Res v => wf_val v
  end.

Lemma wf_env_get ρ x v : wf_env ρ -> M.get x ρ = Some v -> wf_val v.
Proof. intros H; inv H; eauto. Qed.

Lemma wf_env_empty : wf_env (M.empty val).
Proof. constructor; intros x v H. rewrite M.gempty in H. congruence. Qed.

Lemma wf_env_set ρ x v : wf_env ρ -> wf_val v -> wf_env (M.set x v ρ).
Proof.
  intros Hρ Hv. constructor. intros y v' Hget.
  rewrite M.gsspec in Hget. destruct (peq y x); subst.
  - inv Hget; eauto.
  - eapply wf_env_get; eauto.
Qed.

Lemma wf_env_get_list ρ xs vs :
  wf_env ρ -> get_list xs ρ = Some vs -> Forall wf_val vs.
Proof.
  revert vs; induction xs; intros vs Hρ Hget; simpl in *.
  - inv Hget; constructor.
  - destruct (M.get a ρ) eqn:Ha; try congruence.
    destruct (get_list xs ρ) eqn:Hxs; try congruence. inv Hget.
    constructor; eauto. eapply wf_env_get; eauto.
Qed.

Lemma wf_env_set_lists ρ ρ' xs vs :
  wf_env ρ -> Forall wf_val vs -> set_lists xs vs ρ = Some ρ' -> wf_env ρ'.
Proof.
  revert vs ρ'; induction xs; intros vs ρ' Hρ Hvs Hset; destruct vs; simpl in *;
    try (now inv Hset; eauto); try congruence.
  destruct (set_lists xs vs ρ) eqn:Hs; try congruence. inv Hset. inv Hvs.
  eapply wf_env_set; eauto.
Qed.

Lemma wf_env_def_funs B0 B ρ0 ρ :
  wf_env ρ0 -> wf_env ρ -> wf_env (def_funs B0 B ρ0 ρ).
Proof.
  intros H0 H. induction B; simpl; eauto.
  eapply wf_env_set; eauto. constructor; eauto.
Qed.

(** * Free variables, inherited from λANF through erasure *)

Definition occurs_free (e : exp) : Ensemble var := identifiers.occurs_free (erase e).
Definition occurs_free_fundefs (B : fundefs) : Ensemble var :=
  identifiers.occurs_free_fundefs (erase_fundefs B).

Lemma name_in_fundefs_erase B :
  identifiers.name_in_fundefs (erase_fundefs B) <--> name_in_fundefs B.
Proof. induction B; simpl; [ rewrite IHB |]; reflexivity. Qed.

Lemma find_def_erase f B w xs e :
  find_def f B = Some (w, xs, e) -> term.find_def f (erase_fundefs B) = Some (web_tag w, xs, erase e).
Proof.
  induction B; simpl; intros H; try congruence.
  destruct (M.elt_eq f v); subst; eauto. inv H; reflexivity.
Qed.

Lemma find_def_name_in_fundefs f B w xs e :
  find_def f B = Some (w, xs, e) -> name_in_fundefs B f.
Proof.
  induction B; simpl; intros H; try congruence.
  destruct (M.elt_eq f v); subst; [ left; constructor | right; eauto ].
Qed.

Lemma name_in_fundefs_find_def f B :
  name_in_fundefs B f -> exists w xs e, find_def f B = Some (w, xs, e).
Proof.
  induction B; simpl; intros H; [| inv H ].
  destruct (M.elt_eq f v); subst; eauto.
  inv H. inv H0; congruence. eauto.
Qed.

Lemma name_in_fundefs_dec B x : {name_in_fundefs B x} + {~ name_in_fundefs B x}.
Proof.
  destruct (find_def x B) as [[[w xs] e] |] eqn:Hfn.
  - left. eapply find_def_name_in_fundefs; eauto.
  - right. intros Hc. eapply name_in_fundefs_find_def in Hc. destructAll. congruence.
Qed.

Lemma def_funs_neq B0 B ρ0 ρ x :
  ~ name_in_fundefs B x -> M.get x (def_funs B0 B ρ0 ρ) = M.get x ρ.
Proof.
  induction B; simpl; intros Hn; eauto.
  rewrite M.gso; [ eapply IHB | ]; intros Hc; eapply Hn; [ right | left ]; eauto.
  subst; constructor.
Qed.

Lemma def_funs_eq B0 B ρ0 ρ x :
  name_in_fundefs B x -> M.get x (def_funs B0 B ρ0 ρ) = Some (Vfun ρ0 B0 x).
Proof.
  induction B; simpl; intros Hn; inv Hn.
  - inv H. rewrite M.gss; reflexivity.
  - destruct (peq x v); subst; [ rewrite M.gss; reflexivity |].
    rewrite M.gso; eauto.
Qed.

Definition closed_exp (e : exp) : Prop := occurs_free e <--> Empty_set var.

(** Linking: [e1] is evaluated in a thunk and its result is bound to [x] in
    [e2].  The web [w] is the web used for the thunk and its call; linking
    two correct compilation units requires agreeing on it. *)
Definition link (f : var) (w : web) (x : var) (e1 e2 : exp) : exp :=
  Efun (Fcons f w [] e1 Fnil) (Eletapp x f w [] e2).

(** ** Free-variable equations *)

Lemma occurs_free_Econstr x w t ys e :
  occurs_free (Econstr x w t ys e) <--> FromList ys :|: (occurs_free e \\ [set x]).
Proof. exact (identifiers.occurs_free_Econstr x t ys (erase e)). Qed.

Lemma occurs_free_Eprim_val x p e :
  occurs_free (Eprim_val x p e) <--> occurs_free e \\ [set x].
Proof. exact (identifiers.occurs_free_Eprim_val x p (erase e)). Qed.

Lemma occurs_free_Eprim x f ys e :
  occurs_free (Eprim x f ys e) <--> FromList ys :|: (occurs_free e \\ [set x]).
Proof. exact (identifiers.occurs_free_Eprim x f ys (erase e)). Qed.

Lemma occurs_free_Eproj x w t n y e :
  occurs_free (Eproj x w t n y e) <--> [set y] :|: (occurs_free e \\ [set x]).
Proof. exact (identifiers.occurs_free_Eproj x t n y (erase e)). Qed.

Lemma occurs_free_Eletapp x f w ys e :
  occurs_free (Eletapp x f w ys e) <--> (f |: FromList ys) :|: (occurs_free e \\ [set x]).
Proof. exact (identifiers.occurs_free_Eletapp x f (web_tag w) ys (erase e)). Qed.

Lemma occurs_free_Ehalt x : occurs_free (Ehalt x) <--> [set x].
Proof. exact (identifiers.occurs_free_Ehalt x). Qed.

Lemma occurs_free_Eapp f w ys : occurs_free (Eapp f w ys) <--> FromList ys :|: [set f].
Proof. exact (identifiers.occurs_free_Eapp f (web_tag w) ys). Qed.

Lemma occurs_free_Efun B e :
  occurs_free (Efun B e) <--> occurs_free_fundefs B :|: (occurs_free e \\ name_in_fundefs B).
Proof.
  unfold occurs_free, occurs_free_fundefs. simpl.
  rewrite identifiers.occurs_free_Efun, name_in_fundefs_erase. reflexivity.
Qed.

Lemma occurs_free_Ecase_nil x w : occurs_free (Ecase x w []) <--> [set x].
Proof. exact (identifiers.occurs_free_Ecase_nil x). Qed.

Lemma occurs_free_Ecase_cons x w c e P :
  occurs_free (Ecase x w ((c, e) :: P)) <-->
  [set x] :|: (occurs_free e :|: occurs_free (Ecase x w P)).
Proof. exact (identifiers.occurs_free_Ecase_cons x c (erase e) _). Qed.

Lemma occurs_free_fundefs_Fcons f w xs e B :
  occurs_free_fundefs (Fcons f w xs e B) <-->
  (occurs_free e \\ (f |: (FromList xs :|: name_in_fundefs B))) :|:
  (occurs_free_fundefs B \\ [set f]).
Proof.
  unfold occurs_free, occurs_free_fundefs. simpl.
  rewrite identifiers.occurs_free_fundefs_Fcons, name_in_fundefs_erase. reflexivity.
Qed.

Lemma occurs_free_fundefs_Fnil : occurs_free_fundefs Fnil <--> Empty_set var.
Proof. exact identifiers.occurs_free_fundefs_Fnil. Qed.

Lemma occurs_free_in_fun f w xs e B :
  find_def f B = Some (w, xs, e) ->
  occurs_free e \subset FromList xs :|: (name_in_fundefs B :|: occurs_free_fundefs B).
Proof.
  intros Hfn. eapply find_def_erase, identifiers.find_def_correct in Hfn.
  eapply identifiers.occurs_free_in_fun in Hfn.
  unfold occurs_free, occurs_free_fundefs. rewrite <- name_in_fundefs_erase. exact Hfn.
Qed.

Lemma occurs_free_Efun_Included B e :
  occurs_free e \subset occurs_free (Efun B e) :|: name_in_fundefs B.
Proof.
  intros x Hx. destruct (name_in_fundefs_dec B x); [ now right |].
  left. eapply occurs_free_Efun. right. constructor; eauto.
Qed.

Lemma occurs_free_fundefs_Efun_Included B e :
  occurs_free_fundefs B \subset occurs_free (Efun B e).
Proof. intros x Hx. eapply occurs_free_Efun. now left. Qed.

Ltac normalize_occurs_free :=
  repeat match goal with
         | [ |- context[occurs_free (Econstr _ _ _ _ _)] ] => rewrite occurs_free_Econstr
         | [ |- context[occurs_free (Eproj _ _ _ _ _ _)] ] => rewrite occurs_free_Eproj
         | [ |- context[occurs_free (Ecase _ _ [])] ] => rewrite occurs_free_Ecase_nil
         | [ |- context[occurs_free (Ecase _ _ (_ :: _))] ] => rewrite occurs_free_Ecase_cons
         | [ |- context[occurs_free (Eletapp _ _ _ _ _)] ] => rewrite occurs_free_Eletapp
         | [ |- context[occurs_free (Efun _ _)] ] => rewrite occurs_free_Efun
         | [ |- context[occurs_free (Eapp _ _ _)] ] => rewrite occurs_free_Eapp
         | [ |- context[occurs_free (Eprim_val _ _ _)] ] => rewrite occurs_free_Eprim_val
         | [ |- context[occurs_free (Eprim _ _ _ _)] ] => rewrite occurs_free_Eprim
         | [ |- context[occurs_free (Ehalt _)] ] => rewrite occurs_free_Ehalt
         | [ |- context[occurs_free_fundefs (Fcons _ _ _ _ _)] ] => rewrite occurs_free_fundefs_Fcons
         | [ |- context[occurs_free_fundefs Fnil] ] => rewrite occurs_free_fundefs_Fnil
         end.

Lemma fun_body_scope_subset (A B C : Ensemble var) : (A :|: (B :|: C)) \\ A \\ B \subset C.
Proof.
  intros z [[Hz Hx] Hn]. destruct Hz as [z Hz | z Hz]; [ contradiction |].
  destruct Hz as [z Hz | z Hz]; [ contradiction | exact Hz ].
Qed.

(** Membership facts for the variables eliminated by a form *)
Lemma occurs_free_Ecase_scrut x w cl : occurs_free (Ecase x w cl) x.
Proof. unfold occurs_free. rewrite erase_Ecase. constructor. Qed.

Lemma occurs_free_Eproj_scrut x w t n y e : occurs_free (Eproj x w t n y e) y.
Proof. unfold occurs_free. simpl. constructor. Qed.

Lemma occurs_free_Eletapp_fun x f w ys e : occurs_free (Eletapp x f w ys e) f.
Proof. unfold occurs_free. simpl. constructor. now left. Qed.

Lemma occurs_free_Eapp_fun f w ys : occurs_free (Eapp f w ys) f.
Proof. unfold occurs_free. simpl. constructor. Qed.

Lemma occurs_free_Ehalt_var x : occurs_free (Ehalt x) x.
Proof. unfold occurs_free. simpl. constructor. Qed.

Ltac fv_mem :=
  first [ apply occurs_free_Ecase_scrut | apply occurs_free_Eproj_scrut
        | apply occurs_free_Eletapp_fun | apply occurs_free_Eapp_fun
        | apply occurs_free_Ehalt_var ].
