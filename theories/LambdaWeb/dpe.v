(* Flow-directed dead-parameter elimination on λweb (Section 6.1 of the
   paper), for CertiRocq's λANF: mutually recursive bundles, fuel and trace
   postconditions.

   A map [L] assigns to every internal web a liveness mask; [false] at
   position i means that the i-th parameter of every function in the web
   is dead.  Since webs are the unit of transformation, all functions and
   calls of an internal web are transformed together, wherever they occur
   in the program (in particular inside different bundles); exposed webs
   are left unchanged. *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics algebra set_util.
From CertiRocq.LambdaANF Require term term_util.
From CertiRocq.LambdaWeb Require Import syntax semantics exposed post compat dead select indep comp bound.

Import ListNotations.

Open Scope alg_scope.

(** * Live and dead arguments *)

Fixpoint live_args {A} (ys : list A) (bs : list bool) : list A :=
  match bs, ys with
  | b :: bs', y :: ys' => if b then y :: live_args ys' bs' else live_args ys' bs'
  | _, _ => ys
  end.

Fixpoint dead_args {A} (ys : list A) (bs : list bool) : list A :=
  match bs, ys with
  | b :: bs', y :: ys' => if b then dead_args ys' bs' else y :: dead_args ys' bs'
  | _, _ => []
  end.

Lemma live_args_In {A} (xs : list A) bs x : List.In x (live_args xs bs) -> List.In x xs.
Proof.
  revert bs; induction xs; intros bs; destruct bs as [| [] bs]; simpl; eauto.
  intros [Heq | Hin]; eauto.
Qed.

Lemma FromList_live_args {A} (xs : list A) bs : FromList (live_args xs bs) \subset FromList xs.
Proof. intros x Hx. eapply live_args_In; eauto. Qed.

Lemma live_args_get_list {A} (rho : M.t A) ys vs bs :
  get_list ys rho = Some vs -> get_list (live_args ys bs) rho = Some (live_args vs bs).
Proof.
  revert vs bs; induction ys; intros vs bs Hget; simpl in *.
  - inv Hget. destruct bs; reflexivity.
  - destruct (M.get a rho) eqn:Ha; try congruence.
    destruct (get_list ys rho) eqn:Hys; try congruence. inv Hget.
    destruct bs as [| [] bs]; simpl; [ rewrite Ha, Hys | rewrite Ha, (IHys l) | eapply IHys ]; eauto.
Qed.

Lemma live_args_length {A B} (xs : list A) (ys : list B) bs :
  length xs = length ys -> length (live_args xs bs) = length (live_args ys bs).
Proof.
  revert ys bs. induction xs; intros ys bs Hlen; destruct ys; simpl in *; try congruence.
  - destruct bs; reflexivity.
  - inv Hlen. destruct bs as [| [] bs]; simpl; eauto.
Qed.

Lemma FromList_dead_args {A} (xs : list A) bs : FromList (dead_args xs bs) \subset FromList xs.
Proof.
  revert bs; induction xs; intros bs x Hx; destruct bs as [| [] bs]; simpl in *;
    unfold FromList, Ensembles.In in *; simpl in *; try contradiction.
  - right. eapply IHxs; eauto.
  - destruct Hx; eauto. right. eapply IHxs; eauto.
Qed.

Lemma not_live_dead_args {A} (xs : list A) bs x :
  List.In x xs -> ~ List.In x (live_args xs bs) -> List.In x (dead_args xs bs).
Proof.
  revert bs; induction xs; intros bs Hin Hnin; simpl in *; try contradiction.
  destruct bs as [| [] bs]; simpl in *.
  - exfalso; eauto.
  - destruct Hin; [ exfalso; eauto | eapply IHxs; eauto ].
  - destruct Hin; eauto.
Qed.

(** * Specification of the transformation *)

(** Webs with a mask are transformed; the others are left unchanged. *)
Definition sel_L {A} (L : M.t A) (w : web) : bool :=
  match L ! w with Some _ => true | None => false end.

Lemma sel_L_Some {A} (L : M.t A) w a : L ! w = Some a -> sel_L L w = true.
Proof. unfold sel_L. intros H; rewrite H; reflexivity. Qed.

Section DPE_spec.

  Variable (L : M.t (list bool)).

  (** [Gb] bounds the number of dead bindings removed on any path of a
      function body (between two calls); it is the [G] of CertiRocq's
      [inline_bound L G].  The index [n] of [trans n e e'] bounds the number
      of dead bindings removed on any path of [e]. *)
  Variable (Gb : nat).

  Inductive trans : nat -> exp -> exp -> Prop :=
  | Trans_constr :
      forall n x w t ys e e',
        trans n e e' ->
        trans n (Econstr x w t ys e) (Econstr x w t ys e')
  | Trans_proj :
      forall n x w t i y e e',
        trans n e e' ->
        trans n (Eproj x w t i y e) (Eproj x w t i y e')
  | Trans_case_nil :
      forall n x w,
        trans n (Ecase x w []) (Ecase x w [])
  | Trans_case_cons :
      forall n x w c e e' cl cl',
        trans n e e' ->
        trans n (Ecase x w cl) (Ecase x w cl') ->
        trans n (Ecase x w ((c, e) :: cl)) (Ecase x w ((c, e') :: cl'))
  | Trans_letapp_exposed :
      forall n x f w ys e e',
        keeps (sel_L L) w = true ->
        trans n e e' ->
        trans n (Eletapp x f w ys e) (Eletapp x f w ys e')
  | Trans_letapp :
      forall n x f w ys e e' bs,
        exposedb w = false ->
        L ! w = Some bs ->
        trans n e e' ->
        trans n (Eletapp x f w ys e) (Eletapp x f w (live_args ys bs) e')
  | Trans_app_exposed :
      forall n f w ys,
        keeps (sel_L L) w = true ->
        trans n (Eapp f w ys) (Eapp f w ys)
  | Trans_app :
      forall n f w ys bs,
        exposedb w = false ->
        L ! w = Some bs ->
        trans n (Eapp f w ys) (Eapp f w (live_args ys bs))
  | Trans_fun :
      forall n B B' e e',
        trans_fundefs B B' ->
        trans n e e' ->
        trans n (Efun B e) (Efun B' e')
  | Trans_prim_val :
      forall n x p e,
        trans n (Eprim_val x p e) (Eprim_val x p e)
  | Trans_prim :
      forall n x p ys e,
        trans n (Eprim x p ys e) (Eprim x p ys e)
  | Trans_halt :
      forall n x,
        trans n (Ehalt x) (Ehalt x)
  (* dead local bindings: the bound variables do not occur in the
     transformed continuation *)
  | Trans_dead_constr :
      forall n m x w t ys e e',
        trans n e e' -> n < m ->
        ~ occurs_free e' x ->
        trans m (Econstr x w t ys e) e'
  | Trans_dead_proj :
      forall n m x w t i y e e',
        trans n e e' -> n < m ->
        ~ occurs_free e' x ->
        trans m (Eproj x w t i y e) e'
  | Trans_dead_fun :
      forall n m B e e',
        trans n e e' -> n < m ->
        Disjoint _ (name_in_fundefs B) (occurs_free e') ->
        trans m (Efun B e) e'
  with trans_fundefs : fundefs -> fundefs -> Prop :=
  | Trans_Fnil : trans_fundefs Fnil Fnil
  | Trans_Fcons_exposed :
      forall f w xs e e' B B',
        keeps (sel_L L) w = true ->
        trans Gb e e' ->
        trans_fundefs B B' ->
        trans_fundefs (Fcons f w xs e B) (Fcons f w xs e' B')
  | Trans_Fcons :
      forall f w xs e e' B B' bs,
        exposedb w = false ->
        L ! w = Some bs ->
        length bs = length xs ->
        trans Gb e e' ->
        (* dead parameters do not occur in the transformed body *)
        Disjoint _ (FromList (dead_args xs bs)) (occurs_free e') ->
        trans_fundefs B B' ->
        trans_fundefs (Fcons f w xs e B) (Fcons f w (live_args xs bs) e' B').

  Scheme trans_mut := Induction for trans Sort Prop
  with trans_fundefs_mut := Induction for trans_fundefs Sort Prop.

  Combined Scheme trans_mutind from trans_mut, trans_fundefs_mut.

  (** ** Syntactic invariants *)

  Lemma trans_fundefs_names B B' :
    trans_fundefs B B' -> forall f, name_in_fundefs B f <-> name_in_fundefs B' f.
  Proof.
    intros H; induction H; intros g; simpl; try reflexivity;
      split; intros Hin;
      (destruct Hin as [g' Hg | g' Hg]; [ now left | right; now apply IHtrans_fundefs ]).
  Qed.

  Lemma trans_fundefs_names_eq B B' :
    trans_fundefs B B' -> name_in_fundefs B <--> name_in_fundefs B'.
  Proof.
    intros H. split; intros x Hx;
      [ apply (proj1 (trans_fundefs_names _ _ H x)) | apply (proj2 (trans_fundefs_names _ _ H x)) ]; exact Hx.
  Qed.

  Lemma trans_fundefs_find_def B B' f w xs e :
    trans_fundefs B B' ->
    find_def f B = Some (w, xs, e) ->
    exists e',
      trans Gb e e' /\
      ((keeps (sel_L L) w = true /\ find_def f B' = Some (w, xs, e')) \/
       (exists bs, exposedb w = false /\ L ! w = Some bs /\ length bs = length xs /\
                   Disjoint _ (FromList (dead_args xs bs)) (occurs_free e') /\
                   find_def f B' = Some (w, live_args xs bs, e'))).
  Proof.
    intros H; induction H; simpl; intros Hfn; try congruence;
      destruct (M.elt_eq f f0); subst; eauto.
    - inv Hfn. eexists; split; eauto.
    - inv Hfn. eexists; split; eauto. right. eexists; eauto 10.
  Qed.

  Lemma trans_case_tags n x w cl cl' :
    trans n (Ecase x w cl) (Ecase x w cl') -> Forall2 (fun p p' => fst p = fst p') cl cl'.
  Proof.
    revert cl'. induction cl as [| [c e] cl IH]; intros cl' H; inv H; constructor; eauto.
  Qed.

  (** The removal budget can always be enlarged. *)
  Lemma trans_weaken n m e e' : trans n e e' -> n <= m -> trans m e e'.
  Proof.
    intros H; revert m; induction H; intros m' Hle;
      solve [ econstructor; eauto; lia ].
  Qed.

  Lemma trans_occurs_free :
    (forall n e e', trans n e e' -> occurs_free e' \subset occurs_free e) /\
    (forall B B', trans_fundefs B B' -> occurs_free_fundefs B' \subset occurs_free_fundefs B).
  Proof.
    apply trans_mutind; intros; normalize_occurs_free.
    all: repeat match goal with
                | [ Ht : trans_fundefs ?B ?B' |- context[name_in_fundefs ?B'] ] =>
                    rewrite <- (trans_fundefs_names_eq _ _ Ht)
                end.
    all: try solve [ sets ].
    (* dead bindings *)
    all: try solve [ match goal with
             | [ Hb : occurs_free ?e' \subset occurs_free _ |- occurs_free ?e' \subset _ ] =>
                 intros z Hz; right; constructor; [ eapply Hb; exact Hz | intros Hc ];
                 first [ inv Hc; contradiction
                       | match goal with
                         | [ Hd : Disjoint _ (name_in_fundefs _) (occurs_free e') |- _ ] =>
                             eapply Hd; constructor; eassumption
                         end ]
             end ].
    - eapply Included_Union_compat.
      + eapply Included_Union_compat; [ reflexivity | eapply FromList_live_args ].
      + eapply Included_Setminus_compat; [ eassumption | reflexivity ].
    - eapply Included_Union_compat; [ eapply FromList_live_args | reflexivity ].
    - match goal with
      | [ Hd : Disjoint _ (FromList (dead_args ?xs ?bs)) (occurs_free ?e'),
          Hb : occurs_free ?e' \subset occurs_free _ |- _ ] =>
          eapply Included_Union_compat; [| eapply Included_Setminus_compat; [ eassumption | reflexivity ] ];
          intros z [Hz Hn]; constructor; [ eapply Hb; exact Hz |];
          intros Hc; apply Hn; destruct Hc as [z Hc | z Hc]; [ now left |];
          destruct Hc as [z Hc | z Hc]; [| now right; right ];
          right; left;
          destruct (in_dec peq z (live_args xs bs)) as [Hin | Hnin]; [ exact Hin |];
          exfalso; eapply Hd; constructor; [ eapply not_live_dead_args; eauto | exact Hz ]
      end.
  Qed.

End DPE_spec.

(** * The DPE logical relation *)

Section DPE_rel.

  Variable (cenv : term.ctor_env).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Local Notation PostT := (@exposed.PostT fuel trace).
  Local Notation PostGT := (@exposed.PostGT fuel trace).
  Local Notation VTransT := (@exposed.VTransT fuel trace).

  Variables (L : M.t (list bool)) (Gb : nat).

  (** Internal closures: calling the source closure on any arguments is
      related to calling the target closure on the live arguments.  Dead
      arguments are unconstrained (they only need to be well formed). *)
  Definition VT_dpe : VTransT :=
    fun PG V' k v1 v2 =>
      match v1, v2 with
      | Vfun rho1 B1 f1, Vfun rho2 B2 f2 =>
          forall vs1 vs2 j w xs1 e1 rho1',
            find_def f1 B1 = Some (w, xs1, e1) ->
            Some rho1' = set_lists xs1 vs1 (def_funs B1 B1 rho1 rho1) ->
            exists bs e2,
              L ! w = Some bs /\
              find_def f2 B2 = Some (w, live_args xs1 bs, e2) /\
              (length vs2 = length (live_args vs1 bs) ->
               exists rho2',
                 Some rho2' = set_lists (live_args xs1 bs) vs2 (def_funs B2 B2 rho2 rho2) /\
                 (j < k ->
                  Forall wf_val vs1 ->
                  Forall2 (V' j) (live_args vs1 bs) vs2 ->
                  E' cenv V' PG (exposedb w) j (e1, rho1') (e2, rho2')))
      | _, _ => False
      end.

  Global Instance VTransProps_dpe : VTransProps VT_dpe.
  Proof.
    constructor; unfold VT_dpe.
    - intros PG V1 V2 k v1 v2 Hext. destruct v1, v2; try easy.
      intros HVT vs1 vs2 j w xs1 e1 rho1' Hf1 Hs1.
      edestruct HVT as (bs & e2 & HL & Hf2 & Hbody); eauto.
      do 2 eexists. split; [ eassumption | split; [ eassumption |] ].
      intros Hlen. edestruct Hbody as (rho2' & Hs2 & Hb); eauto.
      eexists; split; eauto. intros Hlt Hwf Hall.
      eapply E'_ext; [| eapply Hb; eauto ].
      + intros. eapply Hext. lia.
      + eapply Forall2_monotonic; [| eassumption ]. intros. eapply Hext; eauto.
    - intros PG V k j v1 v2 Hmono. destruct v1, v2; try easy.
      intros HVT Hleq vs1 vs2 i w xs1 e1 rho1' Hf1 Hs1.
      edestruct HVT as (bs & e2 & HL & Hf2 & Hbody); eauto.
      do 2 eexists. split; [ eassumption | split; [ eassumption |] ].
      intros Hlen. edestruct Hbody as (rho2' & Hs2 & Hb); eauto.
      eexists; split; eauto. intros Hlt. eapply Hb. lia.
  Qed.

  (** Closures of webs without a mask keep their calling convention. *)
  Definition VT_dpeS : VTransT := VT_sel cenv (sel_L L) VT_dpe.

  Context (PG : PostGT).

  Notation V := (V cenv VT_dpeS PG).
  Notation E := (E cenv VT_dpeS PG).
  Notation G := (G cenv VT_dpeS PG).
  Notation var_rel := (var_rel cenv VT_dpeS PG).

  Ltac fuel_arith :=
    repeat match goal with
           | [ H : context [ to_nat (_ <+> _) ] |- _ ] => rewrite to_nat_add in H
           | [ |- context [ to_nat (_ <+> _) ] ] => rewrite to_nat_add
           | [ H : context [ to_nat (one_w _) ] |- _ ] => rewrite to_nat_one_w in H
           | [ |- context [ to_nat (one_w _) ] ] => rewrite to_nat_one_w
           end; lia.

  (** ** Environments of transformed functions *)

  Lemma G_set_lists_dpe k S rho1 rho2 rho1' rho2' xs bs vs1 vs2 :
    G k (Setminus _ S (FromList xs)) rho1 rho2 ->
    Forall wf_val vs1 ->
    Forall2 (V k) (live_args vs1 bs) vs2 ->
    Disjoint _ (FromList (dead_args xs bs)) S ->
    set_lists xs vs1 rho1 = Some rho1' ->
    set_lists (live_args xs bs) vs2 rho2 = Some rho2' ->
    G k S rho1' rho2'.
  Proof.
    revert S bs vs1 vs2 rho1' rho2'.
    induction xs as [| x xs IHxs]; intros S bs vs1 vs2 rho1' rho2' HG Hwf Hall Hdis Hs1 Hs2.
    - destruct vs1; simpl in *; try congruence. inv Hs1.
      destruct bs; simpl in *; inv Hall; inv Hs2;
        (eapply (G_antimon cenv VT_dpeS); [ eassumption | rewrite FromList_nil; sets ]).
    - destruct vs1 as [| v1 vs1]; simpl in Hs1; try congruence.
      destruct (set_lists xs vs1 rho1) as [rho1'' |] eqn:Hs1'; try congruence. inv Hs1. inv Hwf.
      destruct bs as [| [] bs]; simpl in *.
      + (* no mask: every argument is live *)
        eapply (G_set_lists cenv VT_dpeS) with (xs := x :: xs) (vs1 := v1 :: vs1) (vs2 := vs2);
          [ eassumption | eassumption | simpl; rewrite Hs1'; reflexivity | exact Hs2 ].
      + inv Hall. destruct (set_lists (live_args xs bs) l' rho2) as [rho2'' |] eqn:Hs2'; try congruence.
        inv Hs2. eapply (G_set cenv VT_dpeS); eauto.
        eapply IHxs; eauto.
        * eapply (G_antimon cenv VT_dpeS); eauto. rewrite FromList_cons.
          intros z Hz. inv Hz. inv H. constructor; eauto. intros Hc. inv Hc; eauto.
        * eapply Disjoint_Included_r; [| eassumption ]. sets.
      + assert (Hx : ~ S x).
        { intros Hc. eapply Hdis. constructor; eauto. now left. }
        eapply (G_set_l_not_in cenv VT_dpeS); eauto.
        eapply IHxs; eauto.
        * eapply (G_antimon cenv VT_dpeS); eauto.
          intros z [Hz Hn]. constructor; [ exact Hz |]. intros Hc.
          unfold FromList, Ensembles.In in Hc. simpl in Hc.
          destruct Hc as [Heq | Hc]; [ subst; contradiction | contradiction ].
        * eapply Disjoint_Included_l; [| eassumption ]. rewrite FromList_cons. sets.
  Qed.

  (** ** Compatibility lemmas for internal calls *)

  Lemma E_app_dpe (P : PostT) ex k rho1 rho2 f w ys bs
        (Hcompat : post_app_compat' f w ys rho1 f w (live_args ys bs) rho2 P PG)
        (HOOT : post_OOT' (Eapp f w ys) rho1 (Eapp f w (live_args ys bs)) rho2 P) :
    exposedb w = false ->
    L ! w = Some bs ->
    wf_env rho1 ->
    var_rel k rho1 rho2 f f ->
    Forall2 (var_rel k rho1 rho2) (live_args ys bs) (live_args ys bs) ->
    E P ex k (Eapp f w ys, rho1) (Eapp f w (live_args ys bs), rho2).
  Proof.
    intros Hw HL Hwf Hfun Hall r1 cin cout Hleq Hstep. inv Hstep.
    - exists OOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H.
      edestruct Hfun as (v2 & Hget2 & Hv); eauto.
      eapply (V_sel_internal cenv (sel_L L) VT_dpe PG) in Hv;
        [| eassumption | eassumption | eapply sel_L_Some; eassumption ].
      destruct v2; try contradiction.
      edestruct var_rel_get_list as (vs2 & Hgetl2 & Hvs); [ eassumption | eapply live_args_get_list; eauto |].
      edestruct (Hv vs vs2 (k - 1)) as (bs' & e2 & HL' & Hf2 & Hbody); eauto.
      rewrite HL in HL'. inv HL'.
      edestruct Hbody as (rho2' & Hset2 & Hb). { symmetry. eapply Forall2_length; eauto. }
      edestruct Hb as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
        [ fuel_arith | eapply wf_env_get_list; eauto | | | eassumption | ].
      + eapply (V_mono_Forall2 cenv VT_dpeS); eauto. lia.
      + fuel_arith.
      + do 3 eexists. split; [| split ].
        * econstructor 2; [ econstructor; eauto |].
          -- congruence.
          -- eapply (R_exposed_ex cenv VT_dpeS); eauto.
        * eapply Hcompat; eauto.
        * eapply (R_mono cenv VT_dpeS); eauto. fuel_arith.
  Qed.

  Lemma E_letapp_dpe (P : PostT) ex k rho1 rho2 x f w ys bs e1 e2
        (Hcompat : post_letapp_compat' cenv x f w ys e1 rho1 x f w (live_args ys bs) e2 rho2 P P PG)
        (HcompatOOT : post_letapp_compat_OOT' x f w ys e1 rho1 x f w (live_args ys bs) e2 rho2 P PG)
        (HOOT : post_OOT' (Eletapp x f w ys e1) rho1 (Eletapp x f w (live_args ys bs) e2) rho2 P) :
    exposedb w = false ->
    L ! w = Some bs ->
    wf_env rho1 ->
    var_rel k rho1 rho2 f f ->
    Forall2 (var_rel k rho1 rho2) (live_args ys bs) (live_args ys bs) ->
    (forall m v1 v2,
        m < k ->
        V m v1 v2 ->
        E P ex m (e1, M.set x v1 rho1) (e2, M.set x v2 rho2)) ->
    E P ex k (Eletapp x f w ys e1, rho1) (Eletapp x f w (live_args ys bs) e2, rho2).
  Proof.
    intros Hw HL Hwf Hfun Hall Hk r1 cin cout Hleq Hstep. inv Hstep.
    - exists OOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H;
        (edestruct Hfun as (v2 & Hget2 & Hv); eauto;
         eapply (V_sel_internal cenv (sel_L L) VT_dpe PG) in Hv;
         [| eassumption | eassumption | eapply sel_L_Some; eassumption ];
         destruct v2; try contradiction;
         edestruct var_rel_get_list as (vs2 & Hgetl2 & Hvs);
         [ eassumption | eapply live_args_get_list; eauto |];
         edestruct (Hv vs vs2 (k - 1)) as (bs' & eb2 & HL' & Hf2 & Hbody); eauto;
         rewrite HL in HL'; inv HL';
         edestruct Hbody as (rho2' & Hset2 & Hb); [ symmetry; eapply Forall2_length; eauto |]).
      + edestruct Hb as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
          [ fuel_arith | eapply wf_env_get_list; eauto | | | eassumption | ].
        * eapply (V_mono_Forall2 cenv VT_dpeS); eauto. lia.
        * fuel_arith.
        * destruct r2 as [| v2]; try contradiction. simpl in HR.
          edestruct (Hk (k - 1 - to_nat cin1)) as (r2 & cin'' & cout'' & Hstep3 & Hpost' & HR');
            [ fuel_arith | eassumption | | eassumption | ]; [ fuel_arith | ].
          do 3 eexists. split; [| split ].
          -- econstructor 2; [ econstructor; eauto |].
             ++ congruence.
             ++ eapply (R_exposed_ex cenv VT_dpeS); eauto.
          -- eapply Hcompat; eauto.
          -- eapply (R_mono cenv VT_dpeS); eauto. fuel_arith.
      + edestruct Hb as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
          [ fuel_arith | eapply wf_env_get_list; eauto | | | eassumption | ].
        * eapply (V_mono_Forall2 cenv VT_dpeS); eauto. lia.
        * fuel_arith.
        * destruct r2; try contradiction.
          do 3 eexists. split; [| split ].
          -- econstructor 2; [ eapply BStept_letapp_oot; eauto; congruence |].
             intros; exact I.
          -- eapply HcompatOOT; eauto.
          -- exact I.
  Qed.

  (** ** Postconditions *)

  (** [P n] relates expressions from which at most [n] dead bindings are
      removed on any path (see [Post_dead]). *)
  Context (P : nat -> PostT) {Hdead : Post_dead cenv P PG Gb}.

  Lemma Hprops_n n : n <= Gb -> Post_properties cenv (P n) (P n) PG.
  Proof. destruct Hdead as [H _ _]. eauto. Qed.

  Lemma P_PG : inclusion _ (P Gb) PG.
  Proof. destruct (Hprops_n Gb (le_n _)); assumption. Qed.

  Lemma P_mono n m : n <= m -> m <= Gb -> inclusion _ (P n) (P m).
  Proof. destruct Hdead as [_ H _]. eauto. Qed.

  Lemma P_src n : n < Gb -> post_source_step (P n) (P (S n)).
  Proof. destruct Hdead as [_ _ H]. eauto. Qed.

  Lemma P_OOT n : n <= Gb -> post_OOT (P n).
  Proof. intros Hn. destruct (Hprops_n n Hn); assumption. Qed.

  (** ** Closures of transformed bundles *)

  Definition IH_exp k :=
    forall m n ex e e' rho1 rho2,
      m < k ->
      n <= Gb ->
      trans L Gb n e e' ->
      G m (occurs_free e') rho1 rho2 ->
      E (P n) ex m (e, rho1) (e', rho2).

  Lemma Vfun_dpe k rho1 rho2 B B' :
    trans_fundefs L Gb B B' ->
    IH_exp k ->
    G k (occurs_free_fundefs B') rho1 rho2 ->
    forall f, name_in_fundefs B f -> V k (Vfun rho1 B f) (Vfun rho2 B' f).
  Proof.
    intros HB. induction k as [k IHk] using lt_wf_rec. intros Hexp HG f Hin.
    assert (Hdefs : forall j, j < k -> forall g, name_in_fundefs B g ->
                                      V j (Vfun rho1 B g) (Vfun rho2 B' g)).
    { intros j Hlt g Hg. eapply IHk; eauto.
      - intros m n ex e e' r1 r2 Hm. eapply Hexp. lia.
      - eapply (G_mono cenv VT_dpeS); eauto. lia. }
    assert (Henv : forall j xs xs' vs1 vs2 rho1' rho2' S,
               j < k ->
               S \subset FromList xs' :|: (name_in_fundefs B' :|: occurs_free_fundefs B') ->
               FromList xs' \subset FromList xs ->
               (forall rho1 rho2, G j (Setminus _ S (FromList xs)) rho1 rho2 ->
                                  set_lists xs vs1 rho1 = Some rho1' ->
                                  set_lists xs' vs2 rho2 = Some rho2' ->
                                  G j S rho1' rho2') ->
               set_lists xs vs1 (def_funs B B rho1 rho1) = Some rho1' ->
               set_lists xs' vs2 (def_funs B' B' rho2 rho2) = Some rho2' ->
               G j S rho1' rho2').
    { intros j xs xs' vs1 vs2 rho1' rho2' S Hlt HS Hxs Hset Hs1 Hs2.
      eapply Hset; eauto.
      eapply (G_def_funs cenv VT_dpeS); try (now apply HG).
      - eapply (G_antimon cenv VT_dpeS). eapply (G_mono cenv VT_dpeS); eauto. lia.
        intros z Hz. inv Hz. inv H. eapply HS in H1. inv H1; [ exfalso; eauto |].
        inv H; eauto. exfalso. eapply H0. eapply trans_fundefs_names; eauto.
      - eapply trans_fundefs_names; eauto.
      - intros g Hg. eapply Hdefs; eauto. }
    edestruct name_in_fundefs_find_def as (w & xs & e & Hfind); eauto.
    edestruct trans_fundefs_find_def as (e' & Htrans & [ [Hw Hfind'] | (bs & Hw & HL & Hlen & Hdis & Hfind') ]);
      eauto.
    - (* exposed function: unchanged calling convention *)
      eapply (V_Vfun_keeps cenv (sel_L L) VT_dpe PG); eauto; try now apply HG.
      eapply (V_fun_def cenv VT_dpeS); eauto.
      intros j vs1 vs2 rho1' rho2' Hlt Hexpv Hvs Hs1 Hs2.
      eapply (E_post_mono cenv VT_dpeS); [ exact P_PG |].
      eapply Hexp; eauto.
      eapply Henv; eauto.
      + eapply occurs_free_in_fun; eauto.
      + reflexivity.
      + intros. eapply G_set_lists; eauto.
    - (* internal function: dead parameters removed *)
      eapply (V_Vfun_sel cenv (sel_L L) VT_dpe PG);
        [ now apply HG | constructor; apply HG | eapply not_exposed_Vfun; eassumption
        | eassumption | eassumption | eapply sel_L_Some; eassumption |].
      + unfold VT_dpe; cbn -[E']. intros vs1 vs2 j w' xs1 e1 rho1' Hf1 Hs1.
        rewrite Hfind in Hf1. inv Hf1.
        exists bs, e'. split; [ eassumption | split; [ eassumption |] ].
        intros Hlen2.
        edestruct (set_lists_length3 (def_funs B' B' rho2 rho2) (live_args xs1 bs) vs2) as [rho2' Hs2].
        { rewrite Hlen2. eapply live_args_length. eapply set_lists_length_eq. symmetry. eassumption. }
        eexists; split; [ symmetry; eassumption |].
        intros Hlt Hwf Hvs.
        eapply (E_post_mono cenv VT_dpeS); [ exact P_PG |].
        eapply Hexp; eauto.
        eapply Henv; eauto.
        * eapply occurs_free_in_fun; eauto.
        * eapply FromList_live_args.
        * intros. eapply G_set_lists_dpe; eauto.
  Qed.

  (** ** Fundamental property *)

  Lemma fundamental k n ex e e' rho1 rho2 :
    n <= Gb ->
    trans L Gb n e e' ->
    G k (occurs_free e') rho1 rho2 ->
    E (P n) ex k (e, rho1) (e', rho2).
  Proof.
    revert n ex e e' rho1 rho2.
    induction k as [k IH] using lt_wf_rec.
    assert (IH' : IH_exp k) by (intros m n ex e e' r1 r2 Hlt; eapply IH; eauto).
    intros n ex e e' rho1 rho2 HnG Htrans. revert ex rho1 rho2 HnG.
    induction Htrans; intros ex rho1 rho2 HnG HG; pose proof (Hprops_n _ HnG) as Hprops'; destruct Hprops'.
    - (* Econstr *)
      eapply (E_constr_compat cenv VT_dpeS); eauto.
      + eapply (G_Forall2_var_rel cenv VT_dpeS); eauto. normalize_occurs_free. sets.
      + intros m v1 v2 Hlt Hv. eapply IH; eauto.
        eapply (G_set cenv VT_dpeS); eauto. eapply (G_antimon cenv VT_dpeS). eapply (G_mono cenv VT_dpeS); eauto. lia.
        normalize_occurs_free. sets.
    - (* Eproj *)
      eapply (E_proj_compat cenv VT_dpeS); eauto.
      + eapply (G_var_rel cenv VT_dpeS); eauto. fv_mem.
      + intros m v1 v2 Hlt Hv. eapply IH; eauto.
        eapply (G_set cenv VT_dpeS); eauto. eapply (G_antimon cenv VT_dpeS). eapply (G_mono cenv VT_dpeS); eauto. lia.
        normalize_occurs_free. sets.
    - (* Ecase [] *)
      eapply (E_case_nil_compat cenv VT_dpeS); eauto.
    - (* Ecase (_ :: _) *)
      eapply (E_case_cons_compat cenv VT_dpeS); eauto.
      + eapply trans_case_tags; eauto.
      + eapply (G_var_rel cenv VT_dpeS); eauto. fv_mem.
      + intros m Hlt. eapply IH; eauto.
        eapply (G_antimon cenv VT_dpeS). eapply (G_mono cenv VT_dpeS); eauto. lia.
        normalize_occurs_free. sets.
      + eapply IHHtrans2; eauto.
        eapply (G_antimon cenv VT_dpeS); eauto. normalize_occurs_free. sets.
    - (* Eletapp, exposed *)
      eapply (E_letapp_compat cenv VT_dpeS); eauto.
      + eapply (var_rel_keeps_fun cenv (sel_L L) VT_dpe PG); eauto. eapply (G_var_rel cenv VT_dpeS); eauto. fv_mem.
      + eapply (G_Forall2_var_rel cenv VT_dpeS); eauto. normalize_occurs_free. sets.
      + intros m v1 v2 Hlt _ Hv. eapply IH; eauto.
        eapply (G_set cenv VT_dpeS); eauto. eapply (G_antimon cenv VT_dpeS). eapply (G_mono cenv VT_dpeS); eauto. lia.
        normalize_occurs_free. sets.
    - (* Eletapp, internal *)
      eapply E_letapp_dpe; eauto.
      + eapply HG.
      + eapply (G_var_rel cenv VT_dpeS); eauto. fv_mem.
      + eapply (G_Forall2_var_rel cenv VT_dpeS); eauto. normalize_occurs_free. sets.
      + intros m v1 v2 Hlt Hv. eapply IH; eauto.
        eapply (G_set cenv VT_dpeS); eauto. eapply (G_antimon cenv VT_dpeS). eapply (G_mono cenv VT_dpeS); eauto. lia.
        normalize_occurs_free. sets.
    - (* Eapp, exposed *)
      eapply (E_app_compat cenv VT_dpeS); eauto.
      + eapply (var_rel_keeps_fun cenv (sel_L L) VT_dpe PG); eauto. eapply (G_var_rel cenv VT_dpeS); eauto. fv_mem.
      + eapply (G_Forall2_var_rel cenv VT_dpeS); eauto. normalize_occurs_free. sets.
    - (* Eapp, internal *)
      eapply E_app_dpe; eauto.
      + eapply HG.
      + eapply (G_var_rel cenv VT_dpeS); eauto. fv_mem.
      + eapply (G_Forall2_var_rel cenv VT_dpeS); eauto. normalize_occurs_free. sets.
    - (* Efun *)
      eapply (E_fun_compat cenv VT_dpeS); eauto.
      eapply (E_mono cenv VT_dpeS) with (k := k); [| lia ].
      eapply IHHtrans; [ exact HnG |].
      eapply (G_antimon cenv VT_dpeS); [| eapply occurs_free_Efun_Included ].
      eapply (G_def_funs cenv VT_dpeS).
      + eapply (G_antimon cenv VT_dpeS); eauto.
        intros z [Hz Hn]. destruct Hz as [z Hz | z Hz]; [ exact Hz |].
        exfalso; apply Hn.
        match goal with
        | [ HB : trans_fundefs _ _ _ _ |- _ ] => apply (proj2 (trans_fundefs_names _ _ _ _ HB z)); exact Hz
        end.
      + eapply HG.
      + eapply HG.
      + eapply trans_fundefs_names; eauto.
      + intros f Hfn. eapply Vfun_dpe; eauto.
        eapply (G_antimon cenv VT_dpeS); eauto. eapply occurs_free_fundefs_Efun_Included.
    - (* Eprim_val *)
      eapply (E_stuck_compat cenv VT_dpeS); eauto. intros. eapply Eprim_val_stuck.
    - (* Eprim *)
      eapply (E_stuck_compat cenv VT_dpeS); eauto. intros. eapply Eprim_stuck.
    - (* Ehalt *)
      eapply (E_halt_compat cenv VT_dpeS); eauto.
      eapply (G_var_rel cenv VT_dpeS); eauto. fv_mem.
    - (* dead Econstr *)
      eapply (E_post_mono cenv VT_dpeS); [ eapply (P_mono (S n)); lia |].
      eapply (E_dead_constr cenv VT_dpeS); [ eapply P_src; lia | eapply P_OOT; lia | eapply HG |].
      intros vs _ Hv. eapply IHHtrans; [ lia |]. eapply (G_set_l_not_in cenv VT_dpeS); eauto.
    - (* dead Eproj *)
      eapply (E_post_mono cenv VT_dpeS); [ eapply (P_mono (S n)); lia |].
      eapply (E_dead_proj cenv VT_dpeS); [ eapply P_src; lia | eapply P_OOT; lia | eapply HG |].
      intros v Hv. eapply IHHtrans; [ lia |]. eapply (G_set_l_not_in cenv VT_dpeS); eauto.
    - (* dead Efun *)
      eapply (E_post_mono cenv VT_dpeS); [ eapply (P_mono (S n)); lia |].
      eapply (E_dead_fun cenv VT_dpeS); [ eapply P_src; lia | eapply P_OOT; lia |].
      eapply IHHtrans; [ lia |]. eapply (G_def_funs_l_not_in cenv VT_dpeS); eauto. eapply HG.
  Qed.

  (** ** Top level *)

  Lemma E_top_dpe n e e' : n <= Gb -> trans L Gb n e e' -> E_top cenv VT_dpeS (P n) PG e e'.
  Proof.
    intros Hn Htrans k rho1 rho2 [HG _] Hbind. eapply fundamental; eauto.
    eapply (G_antimon cenv VT_dpeS); eauto. eapply trans_occurs_free; eauto.
  Qed.

  (** Theorem 5.4 for DPE with dead-binding elimination: the transformed
      program is related to the original one by the λweb relation. *)
  Theorem E_web_dpe_dead n e e' : n <= Gb -> trans L Gb n e e' -> E_web cenv (P n) PG e e'.
  Proof.
    intros Hn Htrans. exact (E_top_E_web cenv VT_dpeS (P n) PG e e' (E_top_dpe n e e' Hn Htrans)).
  Qed.

End DPE_rel.

(** * DPE without dead bindings, for any postcondition *)

Theorem E_web_dpe {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}
        cenv L (P : @exposed.PostT fuel trace) PG {Hprops : Post_properties cenv P P PG} e e' :
  trans L 0 0 e e' -> E_web cenv P PG e e'.
Proof.
  intros Htrans. eapply (E_web_dpe_dead cenv L 0 PG (fun _ => P) 0 e e'); eauto.
Qed.

(** * Refinement, with divergence preservation *)

Section DPE_top.

  Variables (cenv : term.ctor_env) (L : M.t (list bool)) (Gb : nat).

  (** With [dead_bound], the source takes at most [Gb] more steps per call
      than the target, so the target diverges whenever the source does. *)
  Theorem dpe_refines n e e' :
    closed_exp e -> n <= Gb -> trans L Gb n e e' -> refines cenv value_ref e e'.
  Proof.
    intros Hc Hn Htr.
    eapply (E_web_refines cenv (dead_bound n Gb) (dead_bound Gb Gb) (dead_bound_upper_bound n Gb)); eauto.
    eapply (E_web_dpe_dead cenv L Gb (dead_bound Gb Gb) (fun n => dead_bound n Gb)); eauto.
  Qed.

End DPE_top.
