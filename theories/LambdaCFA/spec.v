(* A compositional 0-CFA for λANF: the specification.

   The analysis annotates a λANF program with webs, producing a λweb
   program.  It is compositional: the program may be open and is linked
   against unknown code, so the abstract domain has an element [ltop] for
   the values of the unknown context (the free variables, the arguments of
   exposed functions, the results of unknown functions, ...).

   Abstract values are sets of labels:
   - [ltop]: a value of the unknown context;
   - [lfun f]: a closure of a function named [f];
   - [lcon x]: a constructor allocated at a binding of [x].

   A solution [s] gives a flow set to every variable, abstract arguments
   and results to every function label, abstract fields to every
   constructor label, the set of exposed labels and the internal web of
   every internal label.  Sets may be infinite ([AAll]), which makes the
   trivial solution (everything flows everywhere and is exposed) a
   solution.  Labels need not be unique: the constraints are generated for
   every binding occurrence, so a name bound twice merges both flows.

   The constraints [ok s R e1 e2] relate the λANF program [e1] to its
   annotation [e2]:
   - every use site (call, projection, case) has a web shared by all the
     labels of its flow set, an exposed web if [ltop] is in the set;
   - exposed functions have web [Exposed t] for their λANF tag [t], and
     exposed constructors the interface web [w_con];
   - values flowing to the unknown context are exposed ([esc]).

   The flow sets are flow-insensitive, as in 0-CFA.  [sound.v] proves that
   the constraints imply the annotation relation of [LambdaWeb/anno.v]. *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics set_util.
From CertiRocq.LambdaANF Require term identifiers.
From CertiRocq.LambdaWeb Require Import syntax.

Import ListNotations.

(** * Labels and abstract values *)

Definition lab := positive.
Definition ltop : lab := 1%positive.
Definition lfun (f : var) : lab := xO f.
Definition lcon (x : var) : lab := xI x.

Inductive aset : Type :=
| AFin : PS.t -> aset
| AAll : aset.

Definition ain (l : lab) (A : aset) : Prop :=
  match A with
  | AFin s => PS.In l s
  | AAll => True
  end.

Definition sub (A B : aset) : Prop := forall l, ain l A -> ain l B.

Lemma sub_refl A : sub A A.
Proof. intros l H; exact H. Qed.

Lemma sub_trans A B C : sub A B -> sub B C -> sub A C.
Proof. intros H1 H2 l H. eauto. Qed.

(** * Solutions *)

Record sol : Type :=
  mk_sol { s_var : M.t aset; s_vdef : aset;          (* flow of variables *)
           s_arg : M.t (list aset); s_adef : aset;   (* arguments of function labels *)
           s_fld : M.t (list aset); s_fdef : aset;   (* fields of constructor labels *)
           s_ret : M.t aset; s_rdef : aset;          (* results of function labels *)
           s_ex : aset;                              (* exposed labels *)
           s_iw : M.t positive }.                    (* internal webs of labels *)

Definition getd {A} (m : M.t A) (d : A) (x : positive) : A :=
  match M.get x m with Some a => a | None => d end.

Section Spec.

  Variable (w_con : web).
  Variable (s : sol).

  Definition fl (x : var) : aset := getd (s_var s) (s_vdef s) x.
  Definition Arg (g : var) (i : nat) : aset := nth i (getd (s_arg s) [] g) (s_adef s).
  Definition Fld (z : var) (i : nat) : aset := nth i (getd (s_fld s) [] z) (s_fdef s).
  Definition Ret (g : var) : aset := getd (s_ret s) (s_rdef s) g.

  Definition isex (l : lab) : bool :=
    match s_ex s with
    | AFin e => PS.mem l e
    | AAll => true
    end.

  Lemma isex_ain l : isex l = true <-> ain l (s_ex s).
  Proof.
    unfold isex, ain. destruct (s_ex s); [| tauto ].
    split; intros H; [ eapply PS.mem_spec | eapply PS.mem_spec ]; eauto.
  Qed.

  Definition iweb (l : lab) : web := Internal (getd (s_iw s) 1%positive l).

  (** The web of a function label at a λANF function tag, and the web of a
      constructor label *)
  Definition wfun (g : var) (t : term.fun_tag) : web :=
    if isex (lfun g) then Exposed t else iweb (lfun g).

  Definition wcon (z : var) : web :=
    if isex (lcon z) then w_con else iweb (lcon z).

  (** Escaping sets: every label is the unknown context or exposed *)
  Definition esc (A : aset) : Prop := forall l, ain l A -> l = ltop \/ ain l (s_ex s).

  Lemma esc_sub A B : sub A B -> esc B -> esc A.
  Proof. intros Hs He l Hl. eauto. Qed.

  (** Exposed labels: the arguments of exposed functions come from the
      context, their results and the fields of exposed constructors escape. *)
  Definition labels_ok : Prop :=
    (forall g, ain (lfun g) (s_ex s) -> esc (Ret g) /\ forall i, ain ltop (Arg g i)) /\
    (forall z, ain (lcon z) (s_ex s) -> forall i, esc (Fld z i)).

  (** A use site of [y] (projection or case) with web [w] *)
  Definition use_ok (y : var) (w : web) : Prop :=
    (forall z, ain (lcon z) (fl y) -> wcon z = w) /\
    (ain ltop (fl y) -> w = w_con).

  (** A call site [f ys] with λANF tag [t] and web [w], whose result flows
      to [Rs] *)
  Definition app_ok (f : var) (t : term.fun_tag) (w : web) (ys : list var) (Rs : aset) : Prop :=
    (forall g, ain (lfun g) (fl f) ->
               wfun g t = w /\
               (forall i y, nth_error ys i = Some y -> sub (fl y) (Arg g i)) /\
               sub (Ret g) Rs) /\
    (ain ltop (fl f) -> w = Exposed t /\ ain ltop Rs) /\
    (exposedb w = true -> forall y, List.In y ys -> esc (fl y)).

  (** The constraints.  [R] is the abstract result of the enclosing
      function (or of the program). *)
  Inductive ok : aset -> term.exp -> exp -> Prop :=
  | ok_constr R x c ys e1 e2 :
      ain (lcon x) (fl x) ->
      (forall i y, nth_error ys i = Some y -> sub (fl y) (Fld x i)) ->
      ok R e1 e2 ->
      ok R (term.Econstr x c ys e1) (Econstr x (wcon x) c ys e2)
  | ok_proj R x c n y w e1 e2 :
      use_ok y w ->
      (forall z, ain (lcon z) (fl y) -> sub (Fld z (N.to_nat n)) (fl x)) ->
      (ain ltop (fl y) -> ain ltop (fl x)) ->
      ok R e1 e2 ->
      ok R (term.Eproj x c n y e1) (Eproj x w c n y e2)
  | ok_case_nil R y w :
      use_ok y w ->
      ok R (term.Ecase y []) (Ecase y w [])
  | ok_case_cons R y w c e1 e2 cl1 cl2 :
      ok R e1 e2 ->
      ok R (term.Ecase y cl1) (Ecase y w cl2) ->
      ok R (term.Ecase y ((c, e1) :: cl1)) (Ecase y w ((c, e2) :: cl2))
  | ok_letapp R x f t w ys e1 e2 :
      app_ok f t w ys (fl x) ->
      ok R e1 e2 ->
      ok R (term.Eletapp x f t ys e1) (Eletapp x f w ys e2)
  | ok_fun R B1 B2 e1 e2 :
      ok_fundefs B1 B2 ->
      ok R e1 e2 ->
      ok R (term.Efun B1 e1) (Efun B2 e2)
  | ok_app R f t w ys :
      app_ok f t w ys R ->
      ok R (term.Eapp f t ys) (Eapp f w ys)
  | ok_prim_val R x p e1 e2 :
      ok R e1 e2 ->
      ok R (term.Eprim_val x p e1) (Eprim_val x p e2)
  | ok_prim R x p ys e1 e2 :
      ok R e1 e2 ->
      ok R (term.Eprim x p ys e1) (Eprim x p ys e2)
  | ok_halt R x :
      sub (fl x) R ->
      ok R (term.Ehalt x) (Ehalt x)
  with ok_fundefs : term.fundefs -> fundefs -> Prop :=
  | okf_nil : ok_fundefs term.Fnil Fnil
  | okf_cons g t xs b1 b2 B1 B2 :
      ain (lfun g) (fl g) ->
      (forall i x, nth_error xs i = Some x -> sub (Arg g i) (fl x)) ->
      ok (Ret g) b1 b2 ->
      ok_fundefs B1 B2 ->
      ok_fundefs (term.Fcons g t xs b1 B1) (Fcons g (wfun g t) xs b2 B2).

  Scheme ok_mut := Induction for ok Sort Prop
  with ok_fundefs_mut := Induction for ok_fundefs Sort Prop.

  (** The whole program: its result escapes and its free variables come
      from the context. *)
  Definition ok_top (R : aset) (e1 : term.exp) (e2 : exp) : Prop :=
    labels_ok /\ esc R /\ ok R e1 e2 /\
    (forall x, identifiers.occurs_free e1 x -> ain ltop (fl x)).

  (** ** Properties *)

  Lemma exposedb_wfun g t : exposedb (wfun g t) = isex (lfun g).
  Proof. unfold wfun. destruct (isex (lfun g)); reflexivity. Qed.

  Hypothesis (Hw_con : exposedb w_con = true).

  Lemma exposedb_wcon z : exposedb (wcon z) = isex (lcon z).
  Proof. unfold wcon. destruct (isex (lcon z)); [ exact Hw_con | reflexivity ]. Qed.

  Lemma ok_fundefs_find_def B1 B2 g t xs b1 :
    ok_fundefs B1 B2 ->
    term.find_def g B1 = Some (t, xs, b1) ->
    exists b2, find_def g B2 = Some (wfun g t, xs, b2) /\ ok (Ret g) b1 b2 /\
               ain (lfun g) (fl g) /\
               (forall i x, nth_error xs i = Some x -> sub (Arg g i) (fl x)).
  Proof.
    induction 1; simpl; intros Hfd; try congruence.
    destruct (M.elt_eq g g0); subst.
    - inv Hfd. eauto.
    - eauto.
  Qed.

  Lemma ok_fundefs_names B1 B2 :
    ok_fundefs B1 B2 -> name_in_fundefs B2 <--> identifiers.name_in_fundefs B1.
  Proof. induction 1; simpl; [ reflexivity | rewrite IHok_fundefs; reflexivity ]. Qed.

  Lemma ok_fundefs_find_def_r B1 B2 g w xs b2 :
    ok_fundefs B1 B2 ->
    find_def g B2 = Some (w, xs, b2) ->
    exists t b1, term.find_def g B1 = Some (t, xs, b1) /\ w = wfun g t.
  Proof.
    induction 1; simpl; intros Hfd; try congruence.
    destruct (M.elt_eq g g0); subst.
    - inv Hfd. eauto.
    - eauto.
  Qed.

  Lemma ok_one_case R y w cl1 cl2 :
    ok R (term.Ecase y cl1) (Ecase y w cl2) ->
    Forall2 (fun p p' => fst p = fst p') cl1 (erase_branches cl2).
  Proof.
    revert cl1. induction cl2 as [| [c e2] cl2 IH]; intros cl1 Hok; inv Hok; simpl; constructor; eauto.
  Qed.

  (** The annotated program has the free variables of the original one. *)
  Lemma ok_occurs_free :
    (forall R e1 e2, ok R e1 e2 -> occurs_free e2 <--> identifiers.occurs_free e1) /\
    (forall B1 B2, ok_fundefs B1 B2 ->
                   occurs_free_fundefs B2 <--> identifiers.occurs_free_fundefs B1).
  Proof.
    split; [ eapply (ok_mut (fun R e1 e2 _ => occurs_free e2 <--> identifiers.occurs_free e1)
                            (fun B1 B2 _ => occurs_free_fundefs B2 <--> identifiers.occurs_free_fundefs B1))
           | eapply (ok_fundefs_mut (fun R e1 e2 _ => occurs_free e2 <--> identifiers.occurs_free e1)
                                    (fun B1 B2 _ => occurs_free_fundefs B2 <--> identifiers.occurs_free_fundefs B1)) ];
      intros; normalize_occurs_free;
      repeat match goal with
             | [ |- context[identifiers.occurs_free (term.Econstr _ _ _ _)] ] => rewrite identifiers.occurs_free_Econstr
             | [ |- context[identifiers.occurs_free (term.Eproj _ _ _ _ _)] ] => rewrite identifiers.occurs_free_Eproj
             | [ |- context[identifiers.occurs_free (term.Ecase _ [])] ] => rewrite identifiers.occurs_free_Ecase_nil
             | [ |- context[identifiers.occurs_free (term.Ecase _ (_ :: _))] ] => rewrite identifiers.occurs_free_Ecase_cons
             | [ |- context[identifiers.occurs_free (term.Eletapp _ _ _ _ _)] ] => rewrite identifiers.occurs_free_Eletapp
             | [ |- context[identifiers.occurs_free (term.Efun _ _)] ] => rewrite identifiers.occurs_free_Efun
             | [ |- context[identifiers.occurs_free (term.Eapp _ _ _)] ] => rewrite identifiers.occurs_free_Eapp
             | [ |- context[identifiers.occurs_free (term.Eprim_val _ _ _)] ] => rewrite identifiers.occurs_free_Eprim_val
             | [ |- context[identifiers.occurs_free (term.Eprim _ _ _ _)] ] => rewrite identifiers.occurs_free_Eprim
             | [ |- context[identifiers.occurs_free (term.Ehalt _)] ] => rewrite identifiers.occurs_free_Ehalt
             | [ |- context[identifiers.occurs_free_fundefs (term.Fcons _ _ _ _ _)] ] => rewrite identifiers.occurs_free_fundefs_Fcons
             | [ |- context[identifiers.occurs_free_fundefs term.Fnil] ] => rewrite identifiers.occurs_free_fundefs_Fnil
             end;
      repeat match goal with
             | [ H : _ <--> _ |- _ ] => rewrite H; clear H
             | [ H : ok_fundefs _ _ |- _ ] => rewrite (ok_fundefs_names _ _ H); clear H
             end; reflexivity.
  Qed.

End Spec.
