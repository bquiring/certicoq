(* Erasure from λweb back to λANF (Section 7.4 and Fig. 11 of the paper).

   The erasure relation is a cross-language logical relation: λweb values
   and computations on the left, λANF ones on the right.  Postconditions are
   heterogeneous: they relate a λweb configuration to a λANF one.

   Since every λweb closure, exposed or not, erases to a λANF closure with
   the same behavior, the relation covers all values; a λweb function body
   is evaluated with the exposure flag of its web.  We prove that [erase] is
   in the relation (the fundamental property), that the relation implies
   behavioral refinement (Lemma 7.7) and that it is compatible with linking
   (Lemma 7.8). *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics algebra set_util.
From CertiRocq.LambdaANF Require term term_util identifiers.
From CertiRocq.LambdaANF Require eval rel_comp.
From CertiRocq.LambdaWeb Require Import syntax semantics exposed post compat comp.

Import ListNotations.

Open Scope alg_scope.

Notation aval := term.val.
Notation aenv := CertiRocq.LambdaANF.eval.env.
Notation ares := (@CertiRocq.LambdaANF.eval.res term.val).
Notation aOOT := (@CertiRocq.LambdaANF.eval.OOT term.val).
Notation aRes := (@CertiRocq.LambdaANF.eval.Res term.val).
Notation abstep := CertiRocq.LambdaANF.eval.bstep.
Notation abstep_fuel := CertiRocq.LambdaANF.eval.bstep_fuel.

(** * Erasure with a tag function

    [erase] maps a function web to its index.  The compiler instead gives a
    fresh function tag to each internal web and arity ([retag.v]); erasure
    with a tag function [tagf] covers both.  A call and the function it
    calls share a web and, when the call succeeds, an arity, so they agree
    on the tag. *)

Section EraseT.

  Variable (tagf : web -> nat -> term.fun_tag).

  Fixpoint erase_t (e : exp) : term.exp :=
    match e with
    | Econstr x w t ys e => term.Econstr x t ys (erase_t e)
    | Ecase x w cl =>
        term.Ecase x ((fix erase_t_branches (cl : list (ctor_tag * exp)) :=
                         match cl with
                         | [] => []
                         | (c, e) :: cl => (c, erase_t e) :: erase_t_branches cl
                         end) cl)
    | Eproj x w t n y e => term.Eproj x t n y (erase_t e)
    | Eletapp x f w ys e => term.Eletapp x f (tagf w (length ys)) ys (erase_t e)
    | Efun B e => term.Efun (erase_t_fundefs B) (erase_t e)
    | Eapp f w ys => term.Eapp f (tagf w (length ys)) ys
    | Eprim_val x p e => term.Eprim_val x p (erase_t e)
    | Eprim x p ys e => term.Eprim x p ys (erase_t e)
    | Ehalt x => term.Ehalt x
    end
  with erase_t_fundefs (B : fundefs) : term.fundefs :=
    match B with
    | Fcons f w xs e B => term.Fcons f (tagf w (length xs)) xs (erase_t e) (erase_t_fundefs B)
    | Fnil => term.Fnil
    end.

  Definition erase_t_branches (cl : list (ctor_tag * exp)) : list (ctor_tag * term.exp) :=
    map (fun '(c, e) => (c, erase_t e)) cl.

  Lemma erase_t_branches_inline cl :
    (fix erase_t_branches (cl : list (ctor_tag * exp)) :=
       match cl with
       | [] => []
       | (c, e) :: cl => (c, erase_t e) :: erase_t_branches cl
       end) cl = erase_t_branches cl.
  Proof. induction cl as [| [c e] cl IH]; simpl; congruence. Qed.

  Lemma name_in_fundefs_erase_t B :
    identifiers.name_in_fundefs (erase_t_fundefs B) <--> name_in_fundefs B.
  Proof. induction B; simpl; [ rewrite IHB |]; reflexivity. Qed.

  Lemma find_def_erase_t f B w xs e :
    find_def f B = Some (w, xs, e) ->
    term.find_def f (erase_t_fundefs B) = Some (tagf w (length xs), xs, erase_t e).
  Proof.
    induction B; simpl; intros H; try congruence.
    destruct (M.elt_eq f v); subst; eauto. inv H; reflexivity.
  Qed.

  (** Tags do not change free variables *)
  Lemma occurs_free_erase_t :
    (forall e, identifiers.occurs_free (erase_t e) <--> occurs_free e) /\
    (forall B, identifiers.occurs_free_fundefs (erase_t_fundefs B) <--> occurs_free_fundefs B).
  Proof.
    unfold occurs_free, occurs_free_fundefs.
    eapply exp_fundefs_ind; intros; simpl;
      repeat match goal with
             | |- context [ identifiers.occurs_free (term.Econstr _ _ _ _) ] => rewrite identifiers.occurs_free_Econstr
             | |- context [ identifiers.occurs_free (term.Eproj _ _ _ _ _) ] => rewrite identifiers.occurs_free_Eproj
             | |- context [ identifiers.occurs_free (term.Ecase _ []) ] => rewrite identifiers.occurs_free_Ecase_nil
             | |- context [ identifiers.occurs_free (term.Ecase _ (_ :: _)) ] => rewrite identifiers.occurs_free_Ecase_cons
             | |- context [ identifiers.occurs_free (term.Eletapp _ _ _ _ _) ] => rewrite identifiers.occurs_free_Eletapp
             | |- context [ identifiers.occurs_free (term.Efun _ _) ] => rewrite identifiers.occurs_free_Efun
             | |- context [ identifiers.occurs_free (term.Eapp _ _ _) ] => rewrite identifiers.occurs_free_Eapp
             | |- context [ identifiers.occurs_free (term.Eprim_val _ _ _) ] => rewrite identifiers.occurs_free_Eprim_val
             | |- context [ identifiers.occurs_free (term.Eprim _ _ _ _) ] => rewrite identifiers.occurs_free_Eprim
             | |- context [ identifiers.occurs_free (term.Ehalt _) ] => rewrite identifiers.occurs_free_Ehalt
             | |- context [ identifiers.occurs_free_fundefs (term.Fcons _ _ _ _ _) ] => rewrite identifiers.occurs_free_fundefs_Fcons
             | |- context [ identifiers.occurs_free_fundefs term.Fnil ] => rewrite identifiers.occurs_free_fundefs_Fnil
             end;
      repeat match goal with
             | H : _ <--> _ |- _ => rewrite H; clear H
             end;
      try reflexivity.
    all: rewrite name_in_fundefs_erase_t, <- name_in_fundefs_erase; reflexivity.
  Qed.

End EraseT.

Lemma erase_t_web_tag :
  (forall e, erase_t (fun w _ => web_tag w) e = erase e) /\
  (forall B, erase_t_fundefs (fun w _ => web_tag w) B = erase_fundefs B).
Proof.
  eapply exp_fundefs_ind; intros; simpl; try congruence.
  - inv H0. reflexivity.
Qed.

Section Erase.

  Variable (cenv : term.ctor_env).

  (** The function tags of the λANF side *)
  Variable (tagf : web -> nat -> term.fun_tag).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Local Notation PostT := (@exposed.PostT fuel trace).
  Local Notation PostGT := (@exposed.PostGT fuel trace).
  Local Notation VTransT := (@exposed.VTransT fuel trace).

  (** Heterogeneous postconditions *)
  Definition PostT_e : Type := (exp * env * fuel * trace) -> (term.exp * aenv * fuel * trace) -> Prop.

  Definition R_e' (V : nat -> val -> aval -> Prop) (k : nat) (r1 : res) (r2 : ares) : Prop :=
    match r1, r2 with
    | OOT, CertiRocq.LambdaANF.eval.OOT => True
    | Res v1, CertiRocq.LambdaANF.eval.Res v2 => V k v1 v2
    | _, _ => False
    end.

  Definition E_e' (V : nat -> val -> aval -> Prop) (P : PostT_e) (ex : bool) (k : nat)
             (p1 : exp * env) (p2 : term.exp * aenv) : Prop :=
    let '(e1, rho1) := p1 in
    let '(e2, rho2) := p2 in
    forall r1 cin cout,
      to_nat cin <= k ->
      bstep_fuel cenv ex rho1 e1 cin r1 cout ->
      exists r2 cin' cout',
        abstep_fuel cenv rho2 e2 cin' r2 cout' /\
        P (e1, rho1, cin, cout) (e2, rho2, cin', cout') /\
        R_e' V (k - to_nat cin) r1 r2.

  Definition V_e_fun (PG : PostT_e) (V' : nat -> val -> aval -> Prop) (k : nat) (v1 : val) (v2 : aval) : Prop :=
    match v1, v2 with
    | Vfun rho1 B1 f1, term.Vfun rho2 B2 f2 =>
        forall vs1 vs2 j w xs1 e1 rho1',
          length vs1 = length vs2 ->
          find_def f1 B1 = Some (w, xs1, e1) ->
          Some rho1' = set_lists xs1 vs1 (def_funs B1 B1 rho1 rho1) ->
          exists xs2 e2 rho2',
            term.find_def f2 B2 = Some (tagf w (length xs1), xs2, e2) /\
            Some rho2' = set_lists xs2 vs2 (term.def_funs B2 B2 rho2 rho2) /\
            (j < k ->
             (exposedb w = true -> Forall exposed_val vs1) ->
             Forall2 (V' j) vs1 vs2 ->
             E_e' V' PG (exposedb w) j (e1, rho1') (e2, rho2'))
    | _, _ => False
    end.

  Fixpoint V_e (PG : PostT_e) (k : nat) (v1 : val) (v2 : aval) {struct k} : Prop :=
    let V' : nat -> val -> aval -> Prop :=
      match k with
      | 0 => fun _ _ _ => False
      | S k0 => fun j => V_e PG (k0 - (k0 - j))
      end in
    let fix Vi (v1 : val) (v2 : aval) {struct v1} : Prop :=
      let fix Forall2_aux vs1 vs2 :=
        match vs1, vs2 with
        | [], [] => True
        | v1 :: vs1, v2 :: vs2 => Vi v1 v2 /\ Forall2_aux vs1 vs2
        | _, _ => False
        end in
      match v1, v2 with
      | Vconstr w1 c1 vs1, term.Vconstr c2 vs2 => c1 = c2 /\ Forall2_aux vs1 vs2
      | Vfun _ _ _, _ => V_e_fun PG V' k v1 v2
      | Vprim p1, term.Vprim p2 => p1 = p2
      | Vint z1, term.Vint z2 => z1 = z2
      | _, _ => False
      end
    in Vi v1 v2.

  Definition V_e_ (PG : PostT_e) (k : nat) (v1 : val) (v2 : aval) : Prop :=
    match v1, v2 with
    | Vconstr w1 c1 vs1, term.Vconstr c2 vs2 => c1 = c2 /\ Forall2 (V_e PG k) vs1 vs2
    | Vfun _ _ _, _ => V_e_fun PG (V_e PG) k v1 v2
    | Vprim p1, term.Vprim p2 => p1 = p2
    | Vint z1, term.Vint z2 => z1 = z2
    | _, _ => False
    end.

  Lemma E_e'_ext V1 V2 P ex k p1 p2 :
    (forall j, j <= k -> forall v1 v2, V1 j v1 v2 <-> V2 j v1 v2) ->
    E_e' V1 P ex k p1 p2 -> E_e' V2 P ex k p1 p2.
  Proof.
    destruct p1 as [e1 rho1], p2 as [e2 rho2]. simpl.
    intros Hext HE r1 cin cout Hleq Hstep.
    edestruct HE as (r2 & cin' & cout' & Hstep' & HP & HR); eauto.
    do 3 eexists; split; [ eassumption | split; [ eassumption |] ].
    destruct r1, r2; simpl in *; eauto. eapply Hext; eauto. lia.
  Qed.

  Lemma V_e_fun_ext PG V1 V2 k v1 v2 :
    (forall j, j < k -> forall v1 v2, V1 j v1 v2 <-> V2 j v1 v2) ->
    V_e_fun PG V1 k v1 v2 -> V_e_fun PG V2 k v1 v2.
  Proof.
    destruct v1, v2; cbn -[E_e']; try easy.
    intros Hext Hfn vs1 vs2 j w xs1 e1 rho1' Hlen Hfind Hset.
    edestruct (Hfn vs1 vs2 j w xs1 e1 rho1' Hlen Hfind Hset) as (xs2 & e2 & rho2' & Hfind2 & Hset2 & Hbody).
    do 3 eexists. split; [ eassumption | split; [ eassumption |] ].
    intros Hlt Hexp Hall. eapply E_e'_ext; [| eapply Hbody; eauto ].
    - intros. eapply Hext. lia.
    - eapply Forall2_monotonic; [| eassumption ]. intros. eapply Hext; eauto.
  Qed.

  Lemma V_e_fun_mono PG V k j v1 v2 : V_e_fun PG V k v1 v2 -> j <= k -> V_e_fun PG V j v1 v2.
  Proof.
    destruct v1, v2; cbn -[E_e']; try easy.
    intros Hfn Hleq vs1 vs2 i w xs1 e1 rho1' Hlen Hfind Hset.
    edestruct (Hfn vs1 vs2 i w xs1 e1 rho1' Hlen Hfind Hset) as (xs2 & e2 & rho2' & Hfind2 & Hset2 & Hbody).
    do 3 eexists. split; [ eassumption | split; [ eassumption |] ].
    intros Hlt. eapply Hbody. lia.
  Qed.

  Lemma V_e_eq PG k v1 v2 : V_e PG k v1 v2 <-> V_e_ PG k v1 v2.
  Proof.
    revert v2. induction v1 using val_ind_Forall; intros v2;
      unfold V_e_; destruct k as [| k0]; cbn -[V_e_fun]; try reflexivity.
    - destruct v2; try reflexivity. rewrite Forall2_aux_eq. reflexivity.
    - destruct v2; try reflexivity. rewrite Forall2_aux_eq. reflexivity.
    - split; eapply V_e_fun_ext; intros; lia.
    - split; eapply V_e_fun_ext; intros j Hj; replace (k0 - (k0 - j)) with j by lia; reflexivity.
  Qed.

  Global Opaque V_e.

  Lemma V_e_mono PG k : forall j v1 v2, V_e PG k v1 v2 -> j <= k -> V_e PG j v1 v2.
  Proof.
    intros j v1. revert j. induction v1 using val_ind_Forall; intros j v2 Hv Hleq;
      rewrite V_e_eq in *; unfold V_e_ in *.
    - destruct v2; try contradiction. destructAll. split; eauto.
      revert l H1. induction H; intros l2 Hall; inv Hall; constructor; eauto.
    - eapply V_e_fun_mono; eauto.
    - eauto.
    - eauto.
  Qed.

  Lemma V_e_mono_Forall2 PG k j vs1 vs2 :
    Forall2 (V_e PG k) vs1 vs2 -> j <= k -> Forall2 (V_e PG j) vs1 vs2.
  Proof. intros H Hleq. eapply Forall2_monotonic; [| eassumption ]. intros. eapply V_e_mono; eauto. Qed.

  Lemma R_e_mono PG k j r1 r2 : R_e' (V_e PG) k r1 r2 -> j <= k -> R_e' (V_e PG) j r1 r2.
  Proof. destruct r1, r2; simpl; eauto. intros. eapply V_e_mono; eauto. Qed.

  Definition E_e PG P ex k p1 p2 := E_e' (V_e PG) P ex k p1 p2.

  Lemma E_e_post_mono PG (P1 P2 : PostT_e) ex k p1 p2 :
    (forall c1 c2, P1 c1 c2 -> P2 c1 c2) -> E_e PG P1 ex k p1 p2 -> E_e PG P2 ex k p1 p2.
  Proof.
    destruct p1 as [e1 rho1], p2 as [e2 rho2]. unfold E_e, E_e'.
    intros Hinc HE r1 cin cout Hleq Hstep.
    edestruct HE as (r2 & cin' & cout' & Hstep' & HP & HR); eauto.
    do 3 eexists; split; [ eassumption | split; [ eapply Hinc; eassumption | eassumption ] ].
  Qed.

  (** ** Environments *)

  Definition var_rel_e PG k (rho1 : env) (rho2 : aenv) x y : Prop :=
    forall v1, M.get x rho1 = Some v1 -> exists v2, M.get y rho2 = Some v2 /\ V_e PG k v1 v2.

  Definition G_e PG k (S : Ensemble var) (rho1 : env) (rho2 : aenv) : Prop :=
    forall x, S x -> var_rel_e PG k rho1 rho2 x x.

  Lemma G_e_mono PG k j S rho1 rho2 : G_e PG k S rho1 rho2 -> j <= k -> G_e PG j S rho1 rho2.
  Proof.
    intros HG Hleq x Hx v1 Hget. edestruct HG as (v2 & Hget2 & Hv); eauto.
    eexists; split; eauto. eapply V_e_mono; eauto.
  Qed.

  Lemma G_e_antimon PG k S1 S2 rho1 rho2 : G_e PG k S2 rho1 rho2 -> S1 \subset S2 -> G_e PG k S1 rho1 rho2.
  Proof. intros HG Hsub x Hx. eapply HG. eapply Hsub. eassumption. Qed.

  Lemma G_e_get_list PG k S rho1 rho2 xs vs1 :
    G_e PG k S rho1 rho2 -> FromList xs \subset S -> get_list xs rho1 = Some vs1 ->
    exists vs2, get_list xs rho2 = Some vs2 /\ Forall2 (V_e PG k) vs1 vs2.
  Proof.
    intros HG. revert vs1. induction xs as [| x xs IHxs]; intros vs1 Hsub Hget; simpl in *.
    - inv Hget. eauto.
    - destruct (M.get x rho1) eqn:Hx; try congruence.
      destruct (get_list xs rho1) eqn:Hxs; try congruence. inv Hget.
      edestruct HG as (v2 & Hget2 & Hv); eauto. eapply Hsub. now left.
      edestruct IHxs as (vs2 & Hgetl2 & Hall); eauto.
      intros z Hz. eapply Hsub. now right.
      rewrite Hget2, Hgetl2. eauto.
  Qed.

  Lemma G_e_set PG k S rho1 rho2 x v1 v2 :
    G_e PG k (Setminus _ S [set x]) rho1 rho2 -> V_e PG k v1 v2 ->
    G_e PG k S (M.set x v1 rho1) (M.set x v2 rho2).
  Proof.
    intros HG Hv y Hy v1' Hget. destruct (peq y x); subst.
    - rewrite M.gss in Hget. inv Hget. eexists; rewrite M.gss; eauto.
    - rewrite M.gso in Hget; eauto. rewrite M.gso; eauto.
      eapply HG; eauto. constructor; eauto. intros Hc; inv Hc; eauto.
  Qed.

  Lemma G_e_set_lists PG k S rho1 rho2 rho1' rho2' xs vs1 vs2 :
    G_e PG k (Setminus _ S (FromList xs)) rho1 rho2 ->
    Forall2 (V_e PG k) vs1 vs2 ->
    set_lists xs vs1 rho1 = Some rho1' ->
    set_lists xs vs2 rho2 = Some rho2' ->
    G_e PG k S rho1' rho2'.
  Proof.
    revert S vs1 vs2 rho1' rho2'.
    induction xs as [| x xs IHxs]; intros S vs1 vs2 rho1' rho2' HG Hall Hs1 Hs2;
      destruct vs1, vs2; simpl in *; try congruence; inv Hall.
    - inv Hs1; inv Hs2. eapply G_e_antimon; eauto. rewrite FromList_nil. sets.
    - destruct (set_lists xs vs1 rho1) eqn:Hs1'; try congruence.
      destruct (set_lists xs vs2 rho2) eqn:Hs2'; try congruence. inv Hs1; inv Hs2.
      eapply G_e_set; eauto. eapply IHxs; eauto.
      eapply G_e_antimon; eauto. rewrite FromList_cons. intros z Hz. inv Hz. inv H.
      constructor; eauto. intros Hc. inv Hc. inv H; eauto. eauto.
  Qed.

  Lemma name_in_fundefs_erase' B x :
    identifiers.name_in_fundefs (erase_t_fundefs tagf B) x <-> name_in_fundefs B x.
  Proof. split; intros H; eapply name_in_fundefs_erase_t; eauto. Qed.

  Lemma def_funs_erase_eq B0 B rho0 rho x :
    name_in_fundefs B x ->
    M.get x (term.def_funs (erase_t_fundefs tagf B0) (erase_t_fundefs tagf B) rho0 rho) =
    Some (term.Vfun rho0 (erase_t_fundefs tagf B0) x).
  Proof.
    induction B; simpl; intros Hn; inv Hn.
    - inv H. rewrite M.gss; reflexivity.
    - destruct (peq x v); subst; [ rewrite M.gss; reflexivity |].
      rewrite M.gso; eauto.
  Qed.

  Lemma def_funs_erase_neq B0 B rho0 rho x :
    ~ name_in_fundefs B x ->
    M.get x (term.def_funs (erase_t_fundefs tagf B0) (erase_t_fundefs tagf B) rho0 rho) = M.get x rho.
  Proof.
    induction B; simpl; intros Hn; eauto.
    rewrite M.gso; [ eapply IHB | ]; intros Hc; eapply Hn; [ right | left ]; eauto.
    subst; constructor.
  Qed.

  Lemma G_e_def_funs PG k S rho1 rho2 B rhoc1 rhoc2 :
    G_e PG k (Setminus _ S (name_in_fundefs B)) rho1 rho2 ->
    (forall f, name_in_fundefs B f -> V_e PG k (Vfun rhoc1 B f) (term.Vfun rhoc2 (erase_t_fundefs tagf B) f)) ->
    G_e PG k S (def_funs B B rhoc1 rho1) (term.def_funs (erase_t_fundefs tagf B) (erase_t_fundefs tagf B) rhoc2 rho2).
  Proof.
    intros HG Hfuns x Hx v1 Hget.
    destruct (name_in_fundefs_dec B x) as [Hin | Hnin].
    - rewrite def_funs_eq in Hget; eauto. inv Hget.
      eexists. rewrite def_funs_erase_eq; eauto.
    - rewrite def_funs_neq in Hget; eauto.
      edestruct HG as (v2 & Hget2 & Hv); eauto. constructor; eauto.
      eexists; split; eauto. rewrite def_funs_erase_neq; eauto.
  Qed.

  (** ** Postconditions *)

  Definition post_e_constr (P1 P2 : PostT_e) :=
    forall x w t ys e1 rho1 e2 rho2 vs vs' c1 c2 cout1 cout2,
      get_list ys rho1 = Some vs ->
      get_list ys rho2 = Some vs' ->
      P1 (e1, M.set x (Vconstr w t vs) rho1, c1, cout1) (e2, M.set x (term.Vconstr t vs') rho2, c2, cout2) ->
      P2 (Econstr x w t ys e1, rho1, c1 <+> one_w (Econstr x w t ys e1), cout1 <+> one_w (Econstr x w t ys e1))
         (term.Econstr x t ys e2, rho2, c2 <+> one (term.Econstr x t ys e2), cout2 <+> one (term.Econstr x t ys e2)).

  Definition post_e_proj (P1 P2 : PostT_e) :=
    forall x w t N y e1 rho1 e2 rho2 vs v1 v2 c1 c2 cout1 cout2,
      M.get y rho1 = Some (Vconstr w t vs) ->
      nthN vs N = Some v1 ->
      P1 (e1, M.set x v1 rho1, c1, cout1) (e2, M.set x v2 rho2, c2, cout2) ->
      P2 (Eproj x w t N y e1, rho1, c1 <+> one_w (Eproj x w t N y e1), cout1 <+> one_w (Eproj x w t N y e1))
         (term.Eproj x t N y e2, rho2, c2 <+> one (term.Eproj x t N y e2), cout2 <+> one (term.Eproj x t N y e2)).

  Definition post_e_case_hd (P1 P2 : PostT_e) :=
    forall x w t e1 B1 rho1 e2 B2 rho2 c1 c2 cout1 cout2,
      P1 (e1, rho1, c1, cout1) (e2, rho2, c2, cout2) ->
      P2 (Ecase x w ((t, e1) :: B1), rho1, c1 <+> one_w (Ecase x w ((t, e1) :: B1)), cout1 <+> one_w (Ecase x w ((t, e1) :: B1)))
         (term.Ecase x ((t, e2) :: B2), rho2, c2 <+> one (term.Ecase x ((t, e2) :: B2)), cout2 <+> one (term.Ecase x ((t, e2) :: B2))).

  Definition post_e_case_tl (P1 P2 : PostT_e) :=
    forall x w t e1 B1 rho1 e2 B2 rho2 c1 c2 cout1 cout2,
      P1 (Ecase x w B1, rho1, c1, cout1) (term.Ecase x B2, rho2, c2, cout2) ->
      P2 (Ecase x w ((t, e1) :: B1), rho1, c1, cout1) (term.Ecase x ((t, e2) :: B2), rho2, c2, cout2).

  Definition post_e_fun (P1 P2 : PostT_e) :=
    forall B1 e1 rho1 B2 e2 rho2 c1 c2 cout1 cout2,
      P1 (e1, def_funs B1 B1 rho1 rho1, c1, cout1) (e2, term.def_funs B2 B2 rho2 rho2, c2, cout2) ->
      P2 (Efun B1 e1, rho1, c1 <+> one_w (Efun B1 e1), cout1 <+> one_w (Efun B1 e1))
         (term.Efun B2 e2, rho2, c2 <+> one (term.Efun B2 e2), cout2 <+> one (term.Efun B2 e2)).

  Definition post_e_OOT (P1 : PostT_e) :=
    forall e1 rho1 e2 rho2 c,
      c << one_w e1 -> P1 (e1, rho1, c, <0>) (e2, rho2, c, <0>).

  Definition post_e_base (P1 : PostT_e) :=
    forall x rho1 y rho2,
      P1 (Ehalt x, rho1, one_w (Ehalt x), one_w (Ehalt x)) (term.Ehalt y, rho2, one (term.Ehalt y), one (term.Ehalt y)).

  Definition post_e_app (P PG : PostT_e) :=
    forall f w ys rho1 rho2 xs e1 e2 rhoc1 rhoc2 B h vs rhoc1' c1 c2 cout1 cout2,
      M.get f rho1 = Some (Vfun rhoc1 B h) ->
      get_list ys rho1 = Some vs ->
      find_def h B = Some (w, xs, e1) ->
      set_lists xs vs (def_funs B B rhoc1 rhoc1) = Some rhoc1' ->
      PG (e1, rhoc1', c1, cout1) (e2, rhoc2, c2, cout2) ->
      P (Eapp f w ys, rho1, c1 <+> one_w (Eapp f w ys), cout1 <+> one_w (Eapp f w ys))
        (term.Eapp f (tagf w (length ys)) ys, rho2, c2 <+> one (term.Eapp f (tagf w (length ys)) ys), cout2 <+> one (term.Eapp f (tagf w (length ys)) ys)).

  Definition post_e_letapp (P1 P2 PG : PostT_e) :=
    forall x f f' w ys e1 rho1 e2 rho2 xs e_b1 v1 e_b2 v2
           rhoc1 rhoc2 B h vs rhoc1' c1 c1' c2 c2' cout1 cout2 cout1' cout2',
      M.get f rho1 = Some (Vfun rhoc1 B h) ->
      get_list ys rho1 = Some vs ->
      find_def h B = Some (w, xs, e_b1) ->
      set_lists xs vs (def_funs B B rhoc1 rhoc1) = Some rhoc1' ->
      bstep_fuel cenv (exposedb w) rhoc1' e_b1 c1 (Res v1) cout1 ->
      PG (e_b1, rhoc1', c1, cout1) (e_b2, rhoc2, c2, cout2) ->
      P1 (e1, M.set x v1 rho1, c1', cout1') (e2, M.set x v2 rho2, c2', cout2') ->
      P2 (Eletapp x f w ys e1, rho1, c1 <+> c1' <+> one_w (Eletapp x f w ys e1), cout1 <+> cout1' <+> one_w (Eletapp x f w ys e1))
         (term.Eletapp x f' (tagf w (length ys)) ys e2, rho2, c2 <+> c2' <+> one (term.Eletapp x f' (tagf w (length ys)) ys e2), cout2 <+> cout2' <+> one (term.Eletapp x f' (tagf w (length ys)) ys e2)).

  Definition post_e_letapp_OOT (P2 PG : PostT_e) :=
    forall x f f' w ys e1 rho1 e2 rho2 xs e_b1 e_b2 rhoc1 rhoc2 B h vs rhoc1' c1 c2 cout1 cout2,
      M.get f rho1 = Some (Vfun rhoc1 B h) ->
      get_list ys rho1 = Some vs ->
      find_def h B = Some (w, xs, e_b1) ->
      set_lists xs vs (def_funs B B rhoc1 rhoc1) = Some rhoc1' ->
      PG (e_b1, rhoc1', c1, cout1) (e_b2, rhoc2, c2, cout2) ->
      P2 (Eletapp x f w ys e1, rho1, c1 <+> one_w (Eletapp x f w ys e1), cout1 <+> one_w (Eletapp x f w ys e1))
         (term.Eletapp x f' (tagf w (length ys)) ys e2, rho2, c2 <+> one (term.Eletapp x f' (tagf w (length ys)) ys e2), cout2 <+> one (term.Eletapp x f' (tagf w (length ys)) ys e2)).

  Class Post_properties_e (P1 P2 PG : PostT_e) : Prop :=
    { HPe_con : post_e_constr P1 P2;
      HPe_proj : post_e_proj P1 P2;
      HPe_fun : post_e_fun P1 P2;
      HPe_case_hd : post_e_case_hd P1 P2;
      HPe_case_tl : post_e_case_tl P2 P2;
      HPe_app : post_e_app P1 PG;
      HPe_letapp : post_e_letapp P1 P2 PG;
      HPe_letapp_OOT : post_e_letapp_OOT P1 PG;
      HPe_OOT : post_e_OOT P2;
      HPe_base : post_e_base P2;
      HPe_GPost : forall c1 c2, P1 c1 c2 -> PG c1 c2 }.

  Definition post_e_upper_bound (P : PostT_e) :=
    forall e1 rho1 e2 rho2,
    exists (f : fuel -> fuel),
    forall cin1 cin2 cout1 cout2,
      P (e1, rho1, f cin1, cout1) (e2, rho2, cin2, cout2) ->
      exists (c : fuel), cin2 = (c <+> cin1).

  (** The trivial postcondition *)
  Definition post_e_true : PostT_e := fun _ _ => True.

  Global Instance Post_properties_e_true : Post_properties_e post_e_true post_e_true post_e_true.
  Proof. constructor; unfold post_e_true; repeat intro; exact I. Qed.

  (** ** Fundamental property of erasure *)

  Lemma one_w_one e : one_w e = one (erase_t tagf e).
  Proof. destruct e; reflexivity. Qed.

  Ltac fuel_arith :=
    repeat match goal with
           | [ H : context [ to_nat (_ <+> _) ] |- _ ] => rewrite to_nat_add in H
           | [ |- context [ to_nat (_ <+> _) ] ] => rewrite to_nat_add
           | [ H : context [ to_nat (one_w _) ] |- _ ] => rewrite to_nat_one_w in H
           | [ |- context [ to_nat (one_w _) ] ] => rewrite to_nat_one_w
           | [ H : context [ to_nat (one _) ] |- _ ] => rewrite to_nat_one in H
           | [ |- context [ to_nat (one _) ] ] => rewrite to_nat_one
           end; lia.

  Lemma find_tag_nth_erase cl t e n :
    find_tag_nth cl t e n -> term_util.find_tag_nth (erase_t_branches tagf cl) t (erase_t tagf e) n.
  Proof. intros H; induction H; simpl; constructor; eauto. Qed.



  Section Compat.

  Context (P1 P2 PG : PostT_e).

  Notation E := (E_e PG).
  Notation V := (V_e PG).
  Notation var_rel := (var_rel_e PG).

  Lemma var_rel_e_get_list k rho1 rho2 xs vs1 :
    Forall (fun x => var_rel k rho1 rho2 x x) xs ->
    get_list xs rho1 = Some vs1 ->
    exists vs2, get_list xs rho2 = Some vs2 /\ Forall2 (V k) vs1 vs2.
  Proof.
    revert vs1. induction xs as [| x xs IHxs]; intros vs1 Hall Hget; simpl in *.
    - inv Hget. eauto.
    - inv Hall. destruct (M.get x rho1) eqn:Hx; try congruence.
      destruct (get_list xs rho1) eqn:Hxs; try congruence. inv Hget.
      edestruct H1 as (v2 & Hget2 & Hv); eauto.
      edestruct IHxs as (vs2 & Hgetl2 & Hvs); eauto.
      rewrite Hget2, Hgetl2. eauto.
  Qed.

  Lemma E_e_constr_compat ex k rho1 rho2 x w t ys e1 e2
        (Hcompat : post_e_constr P1 P2) (HOOT : post_e_OOT P2) :
    Forall (fun y => var_rel k rho1 rho2 y y) ys ->
    (forall m v1 v2, m < k -> V m v1 v2 ->
                     E P1 ex m (e1, M.set x v1 rho1) (e2, M.set x v2 rho2)) ->
    E P2 ex k (Econstr x w t ys e1, rho1) (term.Econstr x t ys e2, rho2).
  Proof.
    intros Hall Hk r1 cin cout Hleq Hstep. inv Hstep.
    - exists aOOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H.
      edestruct var_rel_e_get_list as (vs2 & Hget2 & Hvs); eauto.
      edestruct (Hk (k - 1) (Vconstr w t vs) (term.Vconstr t vs2)) as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
        [ fuel_arith | | | eassumption | ].
      + rewrite V_e_eq. split; eauto. eapply V_e_mono_Forall2; eauto. lia.
      + fuel_arith.
      + do 3 eexists. split; [| split ].
        * econstructor 2. econstructor; eauto.
        * eapply Hcompat; eauto.
        * eapply R_e_mono; eauto. fuel_arith.
  Qed.

  Lemma E_e_proj_compat ex k rho1 rho2 x w t n y e1 e2
        (Hcompat : post_e_proj P1 P2) (HOOT : post_e_OOT P2) :
    var_rel k rho1 rho2 y y ->
    (forall m v1 v2, m < k -> V m v1 v2 ->
                     E P1 ex m (e1, M.set x v1 rho1) (e2, M.set x v2 rho2)) ->
    E P2 ex k (Eproj x w t n y e1, rho1) (term.Eproj x t n y e2, rho2).
  Proof.
    intros Hy Hk r1 cin cout Hleq Hstep. inv Hstep.
    - exists aOOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H.
      edestruct Hy as (v2 & Hget2 & Hv); eauto.
      rewrite V_e_eq in Hv. destruct v2; simpl in Hv; try contradiction. destruct Hv as [Heq Hvs]; subst.
      match goal with [ Hn : nthN _ _ = Some _ |- _ ] => destruct (Forall2_nthN _ _ _ _ _ Hvs Hn) as (v2' & Hnth2 & Hv') end.
      edestruct (Hk (k - 1)) as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
        [ fuel_arith | | | eassumption | ].
      + eapply V_e_mono; eauto. lia.
      + fuel_arith.
      + do 3 eexists. split; [| split ].
        * econstructor 2. econstructor; eauto.
        * eapply Hcompat; eauto.
        * eapply R_e_mono; eauto. fuel_arith.
  Qed.

  Lemma E_e_case_nil_compat ex k rho1 rho2 x w (HOOT : post_e_OOT P2) :
    E P2 ex k (Ecase x w [], rho1) (term.Ecase x [], rho2).
  Proof.
    intros r1 cin cout Hleq Hstep. inv Hstep.
    - exists aOOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H. match goal with [ Hft : find_tag_nth [] _ _ _ |- _ ] => inv Hft end.
  Qed.

  Lemma E_e_case_cons_compat ex k rho1 rho2 x w c e1 e2 D1 D2
        (Hcompat_hd : post_e_case_hd P1 P2) (Hcompat_tl : post_e_case_tl P2 P2)
        (HOOT : post_e_OOT P2) :
    Forall2 (fun p p' => fst p = fst p') (erase_branches D1) D2 ->
    var_rel k rho1 rho2 x x ->
    (forall m, m < k -> E P1 ex m (e1, rho1) (e2, rho2)) ->
    E P2 ex k (Ecase x w D1, rho1) (term.Ecase x D2, rho2) ->
    E P2 ex k (Ecase x w ((c, e1) :: D1), rho1) (term.Ecase x ((c, e2) :: D2), rho2).
  Proof.
    intros Hall Henv Hexp_hd Hexp_tl r1 cin cout Hleq Hstep. inv Hstep.
    - exists aOOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H.
      edestruct Henv as (v2 & Hget2 & Hv); eauto.
      rewrite V_e_eq in Hv. destruct v2; simpl in Hv; try contradiction. destruct Hv as [Heq Hvs]; subst.
      match goal with
      | [ Hcs : term_util.caseConsistent _ (erase_branches _) ?tg |- _ ] =>
          assert (Hcc : term_util.caseConsistent cenv ((c, e2) :: D2) tg)
            by (eapply term_util.caseConsistent_same_ctor_tags; [| exact Hcs ]; simpl; constructor; eauto)
      end.
      match goal with [ Hft : find_tag_nth ((_, _) :: _) _ _ _ |- _ ] => inv Hft end.
      + edestruct (Hexp_hd (k - 1)) as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
          [ fuel_arith | | eassumption | ]; [ fuel_arith | ].
        do 3 eexists. split; [| split ].
        * econstructor 2. econstructor; eauto. constructor.
        * eapply Hcompat_hd; eauto.
        * eapply R_e_mono; eauto. fuel_arith.
      + match goal with
        | [ Hc : term_util.caseConsistent _ (erase_branches ((_, _) :: _)) ?tg |- _ ] =>
            assert (Hcc1 : term_util.caseConsistent cenv (erase_branches D1) tg)
              by (simpl in Hc; inv Hc; eassumption)
        end.
        edestruct Hexp_tl as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
          [ | econstructor 2; [ econstructor; eassumption | eassumption ] | ].
        * fuel_arith.
        * inv Hstep2.
          -- destruct r1; try contradiction.
             exists aOOT, cin', <0>. split; [| split ].
             ++ econstructor 1. eassumption.
             ++ eapply Hcompat_tl. eassumption.
             ++ exact I.
          -- match goal with [ Hb : abstep _ _ (term.Ecase _ _) _ _ _ |- _ ] => inv Hb end.
             repeat subst_exp.
             do 3 eexists. split; [| split ].
             ++ econstructor 2. econstructor; eauto. constructor; eauto.
             ++ eapply Hcompat_tl. eassumption.
             ++ eassumption.
  Qed.

  Lemma E_e_halt_compat ex k rho1 rho2 x (HOOT : post_e_OOT P2) (Hbase : post_e_base P2) :
    var_rel k rho1 rho2 x x ->
    E P2 ex k (Ehalt x, rho1) (term.Ehalt x, rho2).
  Proof.
    intros Hvar r1 cin cout Hleq Hstep. inv Hstep.
    - exists aOOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H. edestruct Hvar as (v2 & Hget2 & Hv); eauto.
      do 3 eexists. split; [| split ].
      + econstructor 2. econstructor; eauto.
      + rewrite !plus_zero. eapply Hbase.
      + simpl. eapply V_e_mono; eauto. lia.
  Qed.

  Lemma lt_one_e (c : fuel) e1 (e2 : term.exp) : c << one_w e1 -> c << one e2.
  Proof.
    unfold one_w, algebra.one.
    rewrite (one_eq (exp_to_fin e2) (exp_to_fin (erase e1))). auto.
  Qed.

  Lemma E_e_stuck_compat ex k rho1 rho2 e1 e2 (HOOT : post_e_OOT P2) :
    (forall c r cout, ~ bstep cenv ex rho1 e1 c r cout) ->
    E P2 ex k (e1, rho1) (e2, rho2).
  Proof.
    intros Hstuck r1 cin cout Hleq Hstep. inv Hstep.
    - exists aOOT, cin, <0>. split; [ constructor; eapply lt_one_e; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - exfalso; eapply Hstuck; eauto.
  Qed.

  Lemma E_e_fun_compat ex k rho1 rho2 B1 B2 e1 e2
        (HOOT : post_e_OOT P2) (Hcompat : post_e_fun P1 P2) :
    E P1 ex (k - 1) (e1, def_funs B1 B1 rho1 rho1) (e2, term.def_funs B2 B2 rho2 rho2) ->
    E P2 ex k (Efun B1 e1, rho1) (term.Efun B2 e2, rho2).
  Proof.
    intros Hexp r1 cin cout Hleq Hstep. inv Hstep.
    - exists aOOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H.
      edestruct Hexp as (r2 & cin' & cout' & Hstep2 & Hpost & HR); [| eassumption |]. fuel_arith.
      do 3 eexists. split; [| split ].
      + econstructor 2. econstructor; eauto.
      + eapply Hcompat; eauto.
      + eapply R_e_mono; eauto. fuel_arith.
  Qed.

  (** The tag of the called function is the tag of the call: they have the
      same web, and the call succeeds, so the same arity *)
  Ltac fix_tag ys :=
    match goal with
    | Hf2 : term.find_def _ _ = Some (tagf ?w (length ?xs1), _, _),
      Hs : set_lists ?xs1 ?vs _ = Some _,
      Hg : get_list ys _ = Some ?vs |- _ =>
        let Hl := fresh "Hl" in
        assert (Hl : length xs1 = length ys)
          by (transitivity (length vs); [ eapply set_lists_length_eq; exact Hs
                                        | symmetry; eapply get_list_length_eq; exact Hg ]);
        rewrite Hl in Hf2
    end.

  Lemma E_e_app_compat ex k rho1 rho2 f w ys
        (Hcompat : post_e_app P2 PG) (HOOT : post_e_OOT P2) :
    var_rel k rho1 rho2 f f ->
    Forall (fun y => var_rel k rho1 rho2 y y) ys ->
    E P2 ex k (Eapp f w ys, rho1) (term.Eapp f (tagf w (length ys)) ys, rho2).
  Proof.
    intros Hfun Hall r1 cin cout Hleq Hstep. inv Hstep.
    - exists aOOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H.
      edestruct Hfun as (v2 & Hget2 & Hv); eauto. rewrite V_e_eq in Hv.
      edestruct var_rel_e_get_list as (vs2 & Hgetl2 & Hvs); eauto.
      destruct v2; try contradiction.
      edestruct (Hv vs vs2 (k - 1)) as (xs2 & e2 & rho2' & Hf2 & Hset2 & Hbody); eauto.
      + eapply Forall2_length; eauto.
      + fix_tag ys. edestruct Hbody as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
          [ fuel_arith | eassumption | | | eassumption | ].
        * eapply V_e_mono_Forall2; eauto. lia.
        * fuel_arith.
        * do 3 eexists. split; [| split ].
          -- econstructor 2. econstructor; eauto.
          -- eapply Hcompat; eauto.
          -- eapply R_e_mono; eauto. fuel_arith.
  Qed.

  Lemma E_e_letapp_compat ex k rho1 rho2 x f f' w ys e1 e2
        (Hcompat : post_e_letapp P1 P2 PG) (HcompatOOT : post_e_letapp_OOT P2 PG)
        (HOOT : post_e_OOT P2) :
    var_rel k rho1 rho2 f f' ->
    Forall (fun y => var_rel k rho1 rho2 y y) ys ->
    (forall m v1 v2, m < k -> (exposedb w = true -> exposed_val v1) -> V m v1 v2 ->
                     E P1 ex m (e1, M.set x v1 rho1) (e2, M.set x v2 rho2)) ->
    E P2 ex k (Eletapp x f w ys e1, rho1) (term.Eletapp x f' (tagf w (length ys)) ys e2, rho2).
  Proof.
    intros Hfun Hall Hk r1 cin cout Hleq Hstep. inv Hstep.
    - exists aOOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H;
        (edestruct Hfun as (v2 & Hget2 & Hv); eauto; rewrite V_e_eq in Hv;
         edestruct var_rel_e_get_list as (vs2 & Hgetl2 & Hvs); eauto;
         destruct v2; try contradiction;
         edestruct (Hv vs vs2 (k - 1)) as (xs2 & eb2 & rho2' & Hf2 & Hset2 & Hbody); eauto;
         [ eapply Forall2_length; eauto | fix_tag ys ]).
      + edestruct Hbody as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
          [ fuel_arith | eassumption | | | eassumption | ].
        * eapply V_e_mono_Forall2; eauto. lia.
        * fuel_arith.
        * destruct r2 as [| v2]; try contradiction. simpl in HR.
          edestruct (Hk (k - 1 - to_nat cin1)) as (r2 & cin'' & cout'' & Hstep3 & Hpost' & HR');
            [ fuel_arith | | eassumption | | eassumption | ]; [ eapply bstep_fuel_exposedb; eassumption | fuel_arith | ].
          do 3 eexists. split; [| split ].
          -- econstructor 2. econstructor; eauto.
          -- eapply Hcompat; eauto.
          -- eapply R_e_mono; eauto. fuel_arith.
      + edestruct Hbody as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
          [ fuel_arith | eassumption | | | eassumption | ].
        * eapply V_e_mono_Forall2; eauto. lia.
        * fuel_arith.
        * destruct r2; try contradiction.
          do 3 eexists. split; [| split ].
          -- econstructor 2. eapply CertiRocq.LambdaANF.eval.BStept_letapp_oot; eauto.
          -- eapply HcompatOOT; eauto.
          -- exact I.
  Qed.

  End Compat.

  Context (P : PostT_e) (PG : PostT_e) {Hprops : Post_properties_e P P PG}.

  Lemma P_PG : forall c1 c2, P c1 c2 -> PG c1 c2.
  Proof. destruct Hprops; assumption. Qed.

  Lemma G_e_Forall k S rho1 rho2 ys :
    G_e PG k S rho1 rho2 -> FromList ys \subset S -> Forall (fun y => var_rel_e PG k rho1 rho2 y y) ys.
  Proof.
    intros HG Hsub. induction ys; constructor.
    - eapply HG. eapply Hsub. now left.
    - eapply IHys. intros z Hz. eapply Hsub. now right.
  Qed.

  Lemma erase_t_branches_tags cl :
    Forall2 (fun p p' => fst p = fst p') (erase_branches cl) (erase_t_branches tagf cl).
  Proof. induction cl as [| [c e] cl IH]; simpl; constructor; eauto. Qed.

  Lemma V_e_fun_erase k rho1 rho2 B f :
    (forall m ex e rho1 rho2,
        m < k ->
        G_e PG m (occurs_free e) rho1 rho2 ->
        E_e PG P ex m (e, rho1) (erase_t tagf e, rho2)) ->
    G_e PG k (occurs_free_fundefs B) rho1 rho2 ->
    name_in_fundefs B f ->
    V_e PG k (Vfun rho1 B f) (term.Vfun rho2 (erase_t_fundefs tagf B) f).
  Proof.
    revert f. induction k as [k IHk] using lt_wf_rec. intros f Hexp HG Hin.
    rewrite V_e_eq. unfold V_e_, V_e_fun. cbn -[E_e'].
    intros vs1 vs2 j w xs1 e1 rho1' Hlen Hfind Hset.
    pose proof (find_def_erase_t tagf _ _ _ _ _ Hfind) as Hfind'.
    edestruct (set_lists_length3 (term.def_funs (erase_t_fundefs tagf B) (erase_t_fundefs tagf B) rho2 rho2) xs1 vs2)
      as [rho2' Hset2].
    { rewrite <- Hlen. eapply set_lists_length_eq. symmetry; eauto. }
    do 3 eexists. split; [ eassumption | split; [ symmetry; eassumption |] ].
    intros Hlt Hexpv Hvs.
    eapply E_e_post_mono; [ exact P_PG |].
    eapply Hexp; [ eassumption |].
    eapply G_e_antimon; [| eapply occurs_free_in_fun; eassumption ].
    eapply G_e_set_lists; [| eassumption | symmetry; eassumption | eassumption ].
    eapply G_e_def_funs.
    - eapply G_e_antimon. eapply G_e_mono; eauto. lia.
      eapply fun_body_scope_subset.
    - intros g Hg. eapply IHk; eauto.
      + intros. eapply Hexp; eauto. lia.
      + eapply G_e_mono; eauto. lia.
  Qed.

  Lemma erase_fundamental k ex e rho1 rho2 :
    G_e PG k (occurs_free e) rho1 rho2 ->
    E_e PG P ex k (e, rho1) (erase_t tagf e, rho2).
  Proof.
    revert ex e rho1 rho2.
    induction k as [k IH] using lt_wf_rec.
    intros ex e. revert k IH ex.
    induction e using exp_ind'; intros k IH ex rho1 rho2 HG; pose proof Hprops as Hprops'; destruct Hprops'.
    - eapply E_e_constr_compat; eauto.
      + eapply G_e_Forall; eauto. normalize_occurs_free. sets.
      + intros m v1 v2 Hlt Hv. eapply IHe.
        * intros. eapply IH; eauto. lia.
        * eapply G_e_set; eauto. eapply G_e_antimon. eapply G_e_mono; eauto. lia.
          normalize_occurs_free. sets.
    - eapply E_e_case_nil_compat; eauto.
    - simpl. rewrite (erase_t_branches_inline tagf).
      eapply E_e_case_cons_compat; eauto.
      + eapply erase_t_branches_tags.
      + eapply HG. fv_mem.
      + intros m Hlt. eapply IHe.
        * intros. eapply IH; eauto. lia.
        * eapply G_e_antimon. eapply G_e_mono; eauto. lia.
          normalize_occurs_free. sets.
      + rewrite <- (erase_t_branches_inline tagf). eapply IHe0; eauto.
        eapply G_e_antimon; eauto. normalize_occurs_free. sets.
    - eapply E_e_proj_compat; eauto.
      + eapply HG. fv_mem.
      + intros m v1 v2 Hlt Hv. eapply IHe.
        * intros. eapply IH; eauto. lia.
        * eapply G_e_set; eauto. eapply G_e_antimon. eapply G_e_mono; eauto. lia.
          normalize_occurs_free. sets.
    - eapply E_e_letapp_compat; eauto.
      + eapply HG. fv_mem.
      + eapply G_e_Forall; eauto. normalize_occurs_free. sets.
      + intros m v1 v2 Hlt _ Hv. eapply IHe.
        * intros. eapply IH; eauto. lia.
        * eapply G_e_set; eauto. eapply G_e_antimon. eapply G_e_mono; eauto. lia.
          normalize_occurs_free. sets.
    - eapply E_e_fun_compat; eauto.
      eapply IHe.
      + intros. eapply IH; eauto. lia.
      + eapply G_e_antimon; [| eapply occurs_free_Efun_Included ].
        eapply G_e_def_funs.
        * eapply G_e_antimon. eapply G_e_mono; eauto. lia.
          intros z Hz. inv Hz. inv H; eauto. exfalso; eauto.
        * intros f Hfn. eapply V_e_fun_erase; eauto.
          -- intros. eapply IH; eauto. lia.
          -- eapply G_e_antimon. eapply G_e_mono; eauto. lia.
             eapply occurs_free_fundefs_Efun_Included.
    - eapply E_e_app_compat; eauto.
      + eapply HG. fv_mem.
      + eapply G_e_Forall; eauto. normalize_occurs_free. sets.
    - eapply E_e_stuck_compat; eauto. intros c r cout Hc. inv Hc.
    - eapply E_e_stuck_compat; eauto. intros c r cout Hc. inv Hc.
    - eapply E_e_halt_compat; eauto.
      eapply HG. fv_mem.
  Qed.

  (** Top-level erasure relation *)
  Definition E_erase_top (P : PostT_e) (PG : PostT_e) (e1 : exp) (e2 : term.exp) : Prop :=
    identifiers.occurs_free e2 \subset occurs_free e1 /\
    forall k rho1 rho2,
      G_e PG k (occurs_free e1) rho1 rho2 ->
      term_util.binding_in_map (occurs_free e1) rho1 ->
      E_e PG P true k (e1, rho1) (e2, rho2).

  Theorem erase_correct e : E_erase_top P PG e (erase_t tagf e).
  Proof.
    split; [ eapply (proj1 ((proj1 (occurs_free_erase_t tagf)) e)) |].
    intros k rho1 rho2 HG Hbind. eapply erase_fundamental; eauto.
  Qed.

  (** ** Adequacy (Lemma 7.7) *)

  Fixpoint value_ref_e' (v1 : val) (v2 : aval) : Prop :=
    let fix Forall2_aux vs1 vs2 :=
      match vs1, vs2 with
      | [], [] => True
      | v1 :: vs1, v2 :: vs2 => value_ref_e' v1 v2 /\ Forall2_aux vs1 vs2
      | _, _ => False
      end in
    match v1, v2 with
    | Vconstr _ c1 vs1, term.Vconstr c2 vs2 => c1 = c2 /\ Forall2_aux vs1 vs2
    | Vfun _ _ _, term.Vfun _ _ _ => True
    | Vint i1, term.Vint i2 => i1 = i2
    | Vprim p1, term.Vprim p2 => p1 = p2
    | _, _ => False
    end.

  Lemma V_e_value_ref PG' k v1 v2 : V_e PG' k v1 v2 -> value_ref_e' v1 v2.
  Proof.
    revert v2. induction v1 using val_ind_Forall; intros v2 Hv;
      rewrite V_e_eq in Hv; unfold V_e_ in Hv.
    - destruct v2; try contradiction. destructAll. simpl. split; eauto.
      match goal with [ Ha : Forall2 _ vs ?l |- _ ] => revert l Ha end.
      induction H as [| v vs Hv Hvs IHvs]; intros l2 Hall; inv Hall; simpl;
        [ exact I | split; [ eapply Hv; eassumption | eapply IHvs; eassumption ] ].
    - destruct v2; simpl in *; try contradiction; eauto.
    - destruct v2; try contradiction. simpl; eauto.
    - destruct v2; try contradiction. simpl; eauto.
  Qed.

  Definition aemp_e : aenv := M.empty aval.

  Definition refines_e (vref : val -> aval -> Prop) (e1 : exp) (e2 : term.exp) :=
    (forall v1 c1 t1,
        bstep_fuel cenv true emp e1 c1 (Res v1) t1 ->
        exists v2 c2 t2, abstep_fuel cenv aemp_e e2 c2 (aRes v2) t2 /\ vref v1 v2) /\
    (diverge cenv true emp e1 -> CertiRocq.LambdaANF.eval.diverge cenv aemp_e e2).

  Theorem E_erase_refines P' PG' (HP : post_e_upper_bound P') e1 e2 :
    closed_exp e1 -> E_erase_top P' PG' e1 e2 -> refines_e value_ref_e' e1 e2.
  Proof.
    intros Hc [_ Hrel]. split.
    - intros v1 c1 t1 Hs.
      edestruct (Hrel (to_nat c1) emp aemp_e) as (r2 & c2 & t2 & Hs2 & Hpost & HR);
        [ intros x Hx; eapply Hc in Hx; inv Hx | intros x Hx; eapply Hc in Hx; inv Hx | | eassumption | ].
      + reflexivity.
      + destruct r2 as [| v2]; try contradiction.
        do 3 eexists. split; eauto. eapply V_e_value_ref; eauto.
    - intros Hdiv c2.
      destruct (HP e1 emp e2 aemp_e) as [f Hfn].
      destruct (Hdiv (f c2)) as [t1 Hs].
      edestruct (Hrel (to_nat (f c2)) emp aemp_e) as (r2 & c2' & t2 & Hs2 & Hpost & HR);
        [ intros x Hx; eapply Hc in Hx; inv Hx | intros x Hx; eapply Hc in Hx; inv Hx
        | reflexivity | eassumption | ].
      destruct r2; try contradiction.
      edestruct Hfn as [c Heq]; eauto. subst.
      edestruct CertiRocq.LambdaANF.eval.bstep_fuel_OOT_monotonic as (t2' & c' & Hs2' & _); eauto.
  Qed.

  (** ** Linking (Lemma 7.8) *)

  Variable (lft : term.fun_tag).

  (** Exposed webs keep their λANF tag *)
  Hypothesis (Htag : forall t n, tagf (Exposed t) n = t).

  Theorem E_erase_preserves_linking x e1 e2 e1' e2' :
    closed_exp e1 ->
    occurs_free e1' \subset [set x] ->
    E_erase_top P PG e1 e2 ->
    E_erase_top P PG e1' e2' ->
    E_erase_top P PG (link_w lft x e1 e1') (CertiRocq.LambdaANF.rel_comp.link lft x e2 e2').
  Proof.
    intros Hc Hfv [Hfv1 Hlib] [Hfv2 Hcl]. inv Hprops. split.
    { assert (Hc2 : identifiers.closed_exp e2).
      { split; [| sets ]. eapply Included_trans; [ eassumption | eapply Hc ]. }
      eapply CertiRocq.LambdaANF.rel_comp.link_closed in Hc2; [| eapply Included_trans; eassumption ].
      intros z Hz. eapply Hc2 in Hz. inv Hz. }
    intros k rho1 rho2 HG Hbind.
    unfold CertiRocq.LambdaANF.rel_comp.link, link_w, link.
    (* the tag of the λANF link function is the tag of its exposed web *)
    match goal with
    | |- context [ term.Efun (term.Fcons ?g lft [] ?b term.Fnil) (term.Eletapp ?y ?h lft [] ?k) ] =>
        replace (term.Efun (term.Fcons g lft [] b term.Fnil) (term.Eletapp y h lft [] k))
          with (term.Efun (term.Fcons g (tagf (Exposed lft) (length (@nil var))) [] b term.Fnil)
                          (term.Eletapp y h (tagf (Exposed lft) (length (@nil var))) [] k))
          by (rewrite Htag; reflexivity)
    end.
    eapply E_e_fun_compat; eauto.
    eapply E_e_letapp_compat; eauto.
    - intros v1 Hget. simpl in Hget. rewrite M.gss in Hget. inv Hget.
      eexists. simpl. rewrite M.gss. split; [ reflexivity |].
      rewrite V_e_eq. unfold V_e_, V_e_fun. cbn -[E_e']. intros vs1 vs2 j w xs1 eb1 rho1' Hlen Hfind Hset.
      rewrite peq_true in Hfind. inv Hfind. destruct vs1; simpl in Hset; try congruence.
      destruct vs2; simpl in Hlen; try congruence. inv Hset.
      do 3 eexists. split; [ simpl; rewrite peq_true; reflexivity | split; [ reflexivity |] ].
      intros Hj Hexpv Hall. change (exposedb (Exposed lft)) with true.
      eapply E_e_post_mono; [ eassumption |].
      eapply Hlib.
      + intros z Hz. eapply Hc in Hz. inv Hz.
      + intros z Hz. eapply Hc in Hz. inv Hz.
    - intros m v1 v2 Hlt _ Hv. eapply Hcl.
      + intros z Hz. eapply Hfv in Hz. inv Hz.
        intros v1' Hget. rewrite M.gss in Hget. inv Hget.
        eexists. rewrite M.gss. split; eauto.
      + intros z Hz. eapply Hfv in Hz. inv Hz. eexists. rewrite M.gss. reflexivity.
  Qed.

End Erase.
