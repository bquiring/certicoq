(* Flow-directed constant propagation on λweb (Section 6.2 of the paper),
   for CertiRocq's λANF, with local constants and dead-binding elimination.

   A map [Lc] assigns to every internal web a list with one entry per
   parameter: [Some (c, w)] when every call passes the nullary constructor
   [Vconstr w c []] at that position, [None] otherwise.  Calls of the web no
   longer pass constant arguments, and functions of the web bind the
   corresponding parameters to the constants on entry ([bind_consts]).

   Constants are found locally: the relation carries a scoped environment [K]
   of the variables bound to nullary constructors (by [Econstr x w c []], or
   as constant parameters of the enclosing function), and constant arguments
   of calls must be such variables.  A constant binding whose variable is
   no longer used (typically because the only uses were constant arguments)
   is dropped, as are other dead [Econstr], [Eproj] and [Efun] bindings;
   these removed source steps are counted as in DPE (dpe.v, [Post_dead]). *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics algebra set_util.
From CertiRocq.LambdaANF Require term term_util.
From CertiRocq.LambdaWeb Require Import syntax semantics exposed post compat dead indep comp bound dpe.

Import ListNotations.

Open Scope alg_scope.

(** * Constants *)

Definition const_info : Type := ctor_tag * web.

Definition const_val (i : const_info) : val := let '(c, w) := i in Vconstr w c [].

(** Positions that are still passed *)
Definition cmask (cs : list (option const_info)) : list bool :=
  map (fun c => match c with None => true | Some _ => false end) cs.

(** Bind the constant parameters on function entry *)
Fixpoint bind_consts (xs : list var) (cs : list (option const_info)) (e : exp) : exp :=
  match xs, cs with
  | x :: xs', Some (c, w) :: cs' => Econstr x w c [] (bind_consts xs' cs' e)
  | _ :: xs', None :: cs' => bind_consts xs' cs' e
  | _, _ => e
  end.

(** The environment after [bind_consts] *)
Fixpoint bind_env (xs : list var) (cs : list (option const_info)) (rho : env) : env :=
  match xs, cs with
  | x :: xs', Some i :: cs' => bind_env xs' cs' (M.set x (const_val i) rho)
  | _ :: xs', None :: cs' => bind_env xs' cs' rho
  | _, _ => rho
  end.

(** The source arguments, rebuilt from the target ones *)
Fixpoint pad_consts (cs : list (option const_info)) (vs : list val) : list val :=
  match cs with
  | [] => vs
  | Some i :: cs' => const_val i :: pad_consts cs' vs
  | None :: cs' => match vs with
                   | v :: vs' => v :: pad_consts cs' vs'
                   | [] => []
                   end
  end.

(** Values at constant positions are the constants *)
Fixpoint const_vals (vs : list val) (cs : list (option const_info)) : Prop :=
  match vs, cs with
  | v :: vs', Some i :: cs' => v = const_val i /\ const_vals vs' cs'
  | _ :: vs', None :: cs' => const_vals vs' cs'
  | _, _ => True
  end.

(** Variables at constant positions are known constants *)
Fixpoint const_ok (K : M.t const_info) (ys : list var) (cs : list (option const_info)) : Prop :=
  match ys, cs with
  | y :: ys', Some i :: cs' => K ! y = Some i /\ const_ok K ys' cs'
  | _ :: ys', None :: cs' => const_ok K ys' cs'
  | _, _ => True
  end.

(** Scope of the constant environment *)
Fixpoint param_consts (xs : list var) (cs : list (option const_info)) (K : M.t const_info) :=
  match xs, cs with
  | x :: xs', Some i :: cs' => M.set x i (param_consts xs' cs' K)
  | x :: xs', None :: cs' => M.remove x (param_consts xs' cs' K)
  | x :: xs', [] => M.remove x (param_consts xs' [] K)
  | [], _ => K
  end.

Fixpoint remove_fnames (B : fundefs) (K : M.t const_info) :=
  match B with
  | Fcons f _ _ _ B' => M.remove f (remove_fnames B' K)
  | Fnil => K
  end.

(** The invariant of [K]: its variables are bound to their constants *)
Definition K_inv (K : M.t const_info) (rho : env) :=
  forall x i, K ! x = Some i -> M.get x rho = Some (const_val i).

Lemma K_inv_empty rho : K_inv (M.empty _) rho.
Proof. intros x i H. rewrite M.gempty in H. congruence. Qed.

Lemma K_inv_set K rho x i : K_inv K rho -> K_inv (M.set x i K) (M.set x (const_val i) rho).
Proof.
  intros HK z j Hz. destruct (peq z x); subst.
  - rewrite M.gss in *. congruence.
  - rewrite M.gso in *; eauto.
Qed.

Lemma K_inv_remove K rho x v : K_inv K rho -> K_inv (M.remove x K) (M.set x v rho).
Proof.
  intros HK z j Hz. destruct (peq z x); subst.
  - rewrite M.grs in *. congruence.
  - rewrite M.gro in Hz; eauto. rewrite M.gso; eauto.
Qed.

Lemma K_inv_set_lists K rho rho' xs vs cs :
  K_inv K rho -> const_vals vs cs -> set_lists xs vs rho = Some rho' ->
  K_inv (param_consts xs cs K) rho'.
Proof.
  revert vs cs rho'. induction xs as [| x xs IH]; intros vs cs rho' HK Hc Hs.
  - destruct vs; simpl in Hs; inv Hs. destruct cs; eauto.
  - destruct vs as [| v vs]; simpl in Hs; try congruence.
    destruct (set_lists xs vs rho) as [rho'' |] eqn:Hs'; inv Hs.
    destruct cs as [| [i |] cs]; simpl in *.
    + eapply K_inv_remove. eapply (IH vs []); eauto. destruct vs; exact I.
    + destruct Hc as [Hv Hc]; subst. eapply K_inv_set; eauto.
    + eapply K_inv_remove; eauto.
Qed.

Lemma K_inv_def_funs K rho B0 B rhoc :
  K_inv K rho -> K_inv (remove_fnames B K) (def_funs B0 B rhoc rho).
Proof. induction B; simpl; eauto. intros HK. eapply K_inv_remove; eauto. Qed.

Lemma const_ok_vals K rho ys vs cs :
  K_inv K rho -> const_ok K ys cs -> get_list ys rho = Some vs -> const_vals vs cs.
Proof.
  revert vs cs. induction ys as [| y ys IH]; intros vs cs HK Hok Hget; simpl in *.
  - inv Hget. destruct cs; exact I.
  - destruct (M.get y rho) eqn:Hy; try congruence.
    destruct (get_list ys rho) eqn:Hys; try congruence. inv Hget.
    destruct cs as [| [i |] cs]; simpl in *; eauto.
    destruct Hok as [Hi Hok]. split; eauto. eapply HK in Hi. congruence.
Qed.

(** ** Parameters and arguments *)

Lemma bind_env_set_comm xs cs x v rho :
  ~ List.In x xs -> bind_env xs cs (M.set x v rho) = M.set x v (bind_env xs cs rho).
Proof.
  revert cs rho. induction xs as [| y xs IH]; intros cs rho Hnin; [ destruct cs; reflexivity |].
  destruct cs as [| [i |] cs]; simpl; eauto.
  - rewrite <- IH; [| intros Hc; eapply Hnin; now right ].
    f_equal. eapply M.extensionality. intros z. rewrite !M.gsspec.
    destruct (peq z y); destruct (peq z x); subst; try reflexivity.
    exfalso. eapply Hnin. now left.
  - eapply IH. intros Hc; eapply Hnin; now right.
Qed.

Lemma bind_env_set_lists xs cs vs2 rho rho2 :
  NoDup xs -> length cs = length xs ->
  set_lists (live_args xs (cmask cs)) vs2 rho = Some rho2 ->
  set_lists xs (pad_consts cs vs2) rho = Some (bind_env xs cs rho2).
Proof.
  revert cs vs2 rho2. induction xs as [| x xs IH]; intros cs vs2 rho2 Hnd Hlen Hs.
  - destruct cs; simpl in *; try congruence. destruct vs2; inv Hs. reflexivity.
  - destruct cs as [| c cs]; simpl in *; try congruence. inv Hnd. inv Hlen.
    destruct c as [i |]; simpl in *.
    + erewrite IH; eauto. rewrite bind_env_set_comm; eauto.
    + destruct vs2 as [| v vs2]; simpl in Hs; try congruence.
      destruct (set_lists (live_args xs (cmask cs)) vs2 rho) as [rho2' |] eqn:Hs'; inv Hs.
      erewrite IH; eauto. rewrite bind_env_set_comm; eauto.
Qed.

Lemma Forall2_pad_consts (R : val -> val -> Prop) vs1 vs2 cs :
  length vs1 = length cs ->
  const_vals vs1 cs ->
  Forall2 R (live_args vs1 (cmask cs)) vs2 ->
  (forall i, R (const_val i) (const_val i)) ->
  Forall2 R vs1 (pad_consts cs vs2).
Proof.
  revert vs2 cs. induction vs1 as [| v vs1 IH]; intros vs2 cs Hlen Hc Hall HR.
  - destruct cs; simpl in *; try congruence.
  - destruct cs as [| [i |] cs]; simpl in *; try congruence. inv Hlen.
    + destruct Hc; subst. constructor; eauto.
    + inv Hall. constructor; eauto.
Qed.

Lemma occurs_free_bind_consts xs cs e z :
  occurs_free (bind_consts xs cs e) z ->
  occurs_free e z /\ (List.In z xs -> List.In z (live_args xs (cmask cs))).
Proof.
  revert cs. induction xs as [| x xs IH]; intros cs Hz.
  - destruct cs; simpl in *; split; eauto.
  - destruct cs as [| [[c w] |] cs]; simpl in *.
    + split; eauto.
    + apply (proj1 (occurs_free_Econstr _ _ _ _ _)) in Hz. destruct Hz as [z Hz | z [Hz Hn]];
        [ unfold FromList, Ensembles.In in Hz; simpl in Hz; contradiction |].
      edestruct IH as [Hfv Hin]; eauto. split; eauto.
      intros [Heq | Hin']; [ subst; exfalso; eapply Hn; reflexivity | eauto ].
    + edestruct IH as [Hfv Hin]; eauto. split; eauto.
      intros [Heq | Hin']; [ now left | right; eauto ].
Qed.

Lemma occurs_free_bind_consts_r xs cs e z :
  occurs_free e z -> ~ List.In z xs -> occurs_free (bind_consts xs cs e) z.
Proof.
  revert cs. induction xs as [| x xs IH]; intros cs Hz Hnin.
  - destruct cs; eauto.
  - destruct cs as [| [[c w] |] cs]; simpl; eauto.
    + apply (proj2 (occurs_free_Econstr _ _ _ _ _)). right. constructor.
      * eapply IH; eauto. intros Hc; eapply Hnin; now right.
      * intros Hc; inv Hc. eapply Hnin; now left.
    + eapply IH; eauto. intros Hc; eapply Hnin; now right.
Qed.

(** * Specification of the transformation *)

Section CP_spec.

  Variables (Lc : M.t (list (option const_info))) (Gb : nat).

  Inductive trans : M.t const_info -> nat -> exp -> exp -> Prop :=
  | Trans_constr_const :
      forall K n x w c e e',
        trans (M.set x (c, w) K) n e e' ->
        trans K n (Econstr x w c [] e) (Econstr x w c [] e')
  | Trans_constr :
      forall K n x w t ys e e',
        trans (M.remove x K) n e e' ->
        trans K n (Econstr x w t ys e) (Econstr x w t ys e')
  | Trans_proj :
      forall K n x w t i y e e',
        trans (M.remove x K) n e e' ->
        trans K n (Eproj x w t i y e) (Eproj x w t i y e')
  | Trans_case_nil :
      forall K n x w,
        trans K n (Ecase x w []) (Ecase x w [])
  | Trans_case_cons :
      forall K n x w c e e' cl cl',
        trans K n e e' ->
        trans K n (Ecase x w cl) (Ecase x w cl') ->
        trans K n (Ecase x w ((c, e) :: cl)) (Ecase x w ((c, e') :: cl'))
  | Trans_letapp_exposed :
      forall K n x f w ys e e',
        exposedb w = true ->
        trans (M.remove x K) n e e' ->
        trans K n (Eletapp x f w ys e) (Eletapp x f w ys e')
  | Trans_letapp :
      forall K n x f w ys e e' cs,
        exposedb w = false ->
        Lc ! w = Some cs ->
        const_ok K ys cs ->
        trans (M.remove x K) n e e' ->
        trans K n (Eletapp x f w ys e) (Eletapp x f w (live_args ys (cmask cs)) e')
  | Trans_app_exposed :
      forall K n f w ys,
        exposedb w = true ->
        trans K n (Eapp f w ys) (Eapp f w ys)
  | Trans_app :
      forall K n f w ys cs,
        exposedb w = false ->
        Lc ! w = Some cs ->
        const_ok K ys cs ->
        trans K n (Eapp f w ys) (Eapp f w (live_args ys (cmask cs)))
  | Trans_fun :
      forall K n B B' e e',
        trans_fundefs (remove_fnames B K) B B' ->
        trans (remove_fnames B K) n e e' ->
        trans K n (Efun B e) (Efun B' e')
  | Trans_prim_val :
      forall K n x p e,
        trans K n (Eprim_val x p e) (Eprim_val x p e)
  | Trans_prim :
      forall K n x p ys e,
        trans K n (Eprim x p ys e) (Eprim x p ys e)
  | Trans_halt :
      forall K n x,
        trans K n (Ehalt x) (Ehalt x)
  (* dead local bindings; a dead constant is still known *)
  | Trans_dead_constr_const :
      forall K n m x w c e e',
        trans (M.set x (c, w) K) n e e' -> n < m ->
        ~ occurs_free e' x ->
        trans K m (Econstr x w c [] e) e'
  | Trans_dead_constr :
      forall K n m x w t ys e e',
        trans (M.remove x K) n e e' -> n < m ->
        ~ occurs_free e' x ->
        trans K m (Econstr x w t ys e) e'
  | Trans_dead_proj :
      forall K n m x w t i y e e',
        trans (M.remove x K) n e e' -> n < m ->
        ~ occurs_free e' x ->
        trans K m (Eproj x w t i y e) e'
  | Trans_dead_fun :
      forall K n m B e e',
        trans (remove_fnames B K) n e e' -> n < m ->
        Disjoint _ (name_in_fundefs B) (occurs_free e') ->
        trans K m (Efun B e) e'
  with trans_fundefs : M.t const_info -> fundefs -> fundefs -> Prop :=
  | Trans_Fnil : forall K, trans_fundefs K Fnil Fnil
  | Trans_Fcons_exposed :
      forall K f w xs e e' B B',
        exposedb w = true ->
        trans (param_consts xs [] K) Gb e e' ->
        trans_fundefs K B B' ->
        trans_fundefs K (Fcons f w xs e B) (Fcons f w xs e' B')
  | Trans_Fcons :
      forall K f w xs e e' B B' cs,
        exposedb w = false ->
        Lc ! w = Some cs ->
        length cs = length xs ->
        NoDup xs ->
        trans (param_consts xs cs K) Gb e e' ->
        trans_fundefs K B B' ->
        trans_fundefs K (Fcons f w xs e B)
                      (Fcons f w (live_args xs (cmask cs)) (bind_consts xs cs e') B').

  Scheme trans_mut := Induction for trans Sort Prop
  with trans_fundefs_mut := Induction for trans_fundefs Sort Prop.

  Combined Scheme trans_mutind from trans_mut, trans_fundefs_mut.

  (** ** Syntactic invariants *)

  Lemma trans_weaken K n m e e' : trans K n e e' -> n <= m -> trans K m e e'.
  Proof.
    intros H; revert m; induction H; intros m' Hle;
      solve [ econstructor; eauto; lia ].
  Qed.

  Lemma trans_fundefs_names K B B' :
    trans_fundefs K B B' -> forall f, name_in_fundefs B f <-> name_in_fundefs B' f.
  Proof.
    intros H; induction H; intros g; simpl; try reflexivity;
      split; intros Hin;
      (destruct Hin as [g' Hg | g' Hg]; [ now left | right; now apply IHtrans_fundefs ]).
  Qed.

  Lemma trans_fundefs_names_eq K B B' :
    trans_fundefs K B B' -> name_in_fundefs B <--> name_in_fundefs B'.
  Proof.
    intros H. split; intros x Hx;
      [ apply (proj1 (trans_fundefs_names _ _ _ H x)) | apply (proj2 (trans_fundefs_names _ _ _ H x)) ]; exact Hx.
  Qed.

  Lemma trans_fundefs_find_def K B B' f w xs e :
    trans_fundefs K B B' ->
    find_def f B = Some (w, xs, e) ->
    exists e',
      (exposedb w = true /\ trans (param_consts xs [] K) Gb e e' /\
       find_def f B' = Some (w, xs, e')) \/
      (exists cs, exposedb w = false /\ Lc ! w = Some cs /\ length cs = length xs /\ NoDup xs /\
                  trans (param_consts xs cs K) Gb e e' /\
                  find_def f B' = Some (w, live_args xs (cmask cs), bind_consts xs cs e')).
  Proof.
    intros H; induction H; simpl; intros Hfn; try congruence;
      destruct (M.elt_eq f f0); subst; eauto.
    - inv Hfn. eexists; left; eauto.
    - inv Hfn. eexists; right. eexists; eauto 10.
  Qed.

  Lemma trans_case_tags K n x w cl cl' :
    trans K n (Ecase x w cl) (Ecase x w cl') -> Forall2 (fun p p' => fst p = fst p') cl cl'.
  Proof.
    revert cl'. induction cl as [| [c e] cl IH]; intros cl' H; inv H; constructor; eauto.
  Qed.

  Lemma trans_occurs_free :
    (forall K n e e', trans K n e e' -> occurs_free e' \subset occurs_free e) /\
    (forall K B B', trans_fundefs K B B' -> occurs_free_fundefs B' \subset occurs_free_fundefs B).
  Proof.
    apply trans_mutind; intros; normalize_occurs_free.
    all: repeat match goal with
                | [ Ht : trans_fundefs _ ?B ?B' |- context[name_in_fundefs ?B'] ] =>
                    rewrite <- (trans_fundefs_names_eq _ _ _ Ht)
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
      | [ Hb : occurs_free ?e' \subset occurs_free _ |- _ ] =>
          eapply Included_Union_compat; [| eapply Included_Setminus_compat; [ eassumption | reflexivity ] ];
          intros z [Hz Hn]; edestruct occurs_free_bind_consts as [Hfv Hin]; [ exact Hz |];
          constructor; [ eapply Hb; exact Hfv |];
          intros Hc; apply Hn; destruct Hc as [z Hc | z Hc]; [ now left |];
          destruct Hc as [z Hc | z Hc]; [| now right; right ];
          right; left; eapply Hin; exact Hc
      end.
  Qed.

End CP_spec.

(** * The constant propagation logical relation *)

Section CP_rel.

  Variable (cenv : term.ctor_env).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Local Notation PostT := (@exposed.PostT fuel trace).
  Local Notation PostGT := (@exposed.PostGT fuel trace).
  Local Notation VTransT := (@exposed.VTransT fuel trace).

  Variables (Lc : M.t (list (option const_info))) (Gb : nat).

  (** Internal closures: calling the source closure on arguments whose
      constant positions hold the constants is related to calling the
      target closure on the remaining arguments. *)
  Definition VT_cp : VTransT :=
    fun PG V' k v1 v2 =>
      match v1, v2 with
      | Vfun rho1 B1 f1, Vfun rho2 B2 f2 =>
          forall vs1 vs2 j w xs1 e1 rho1',
            find_def f1 B1 = Some (w, xs1, e1) ->
            Some rho1' = set_lists xs1 vs1 (def_funs B1 B1 rho1 rho1) ->
            exists cs e2,
              Lc ! w = Some cs /\
              find_def f2 B2 = Some (w, live_args xs1 (cmask cs), e2) /\
              (length vs2 = length (live_args vs1 (cmask cs)) ->
               exists rho2',
                 Some rho2' = set_lists (live_args xs1 (cmask cs)) vs2 (def_funs B2 B2 rho2 rho2) /\
                 (j < k ->
                  Forall wf_val vs1 ->
                  const_vals vs1 cs ->
                  Forall2 (V' j) (live_args vs1 (cmask cs)) vs2 ->
                  E' cenv V' PG (exposedb w) j (e1, rho1') (e2, rho2')))
      | _, _ => False
      end.

  Global Instance VTransProps_cp : VTransProps VT_cp.
  Proof.
    constructor; unfold VT_cp.
    - intros PG V1 V2 k v1 v2 Hext. destruct v1, v2; try easy.
      intros HVT vs1 vs2 j w xs1 e1 rho1' Hf1 Hs1.
      edestruct HVT as (cs & e2 & HL & Hf2 & Hbody); eauto.
      do 2 eexists. split; [ eassumption | split; [ eassumption |] ].
      intros Hlen. edestruct Hbody as (rho2' & Hs2 & Hb); eauto.
      eexists; split; eauto. intros Hlt Hwf Hc Hall.
      eapply E'_ext; [| eapply Hb; eauto ].
      + intros. eapply Hext. lia.
      + eapply Forall2_monotonic; [| eassumption ]. intros. eapply Hext; eauto.
    - intros PG V k j v1 v2 Hmono. destruct v1, v2; try easy.
      intros HVT Hleq vs1 vs2 i w xs1 e1 rho1' Hf1 Hs1.
      edestruct HVT as (cs & e2 & HL & Hf2 & Hbody); eauto.
      do 2 eexists. split; [ eassumption | split; [ eassumption |] ].
      intros Hlen. edestruct Hbody as (rho2' & Hs2 & Hb); eauto.
      eexists; split; eauto. intros Hlt. eapply Hb. lia.
  Qed.

  Context (PG : PostGT).

  Notation V := (V cenv VT_cp PG).
  Notation E := (E cenv VT_cp PG).
  Notation G := (G cenv VT_cp PG).
  Notation var_rel := (var_rel cenv VT_cp PG).

  Ltac fuel_arith :=
    repeat match goal with
           | [ H : context [ to_nat (_ <+> _) ] |- _ ] => rewrite to_nat_add in H
           | [ |- context [ to_nat (_ <+> _) ] ] => rewrite to_nat_add
           | [ H : context [ to_nat (one_w _) ] |- _ ] => rewrite to_nat_one_w in H
           | [ |- context [ to_nat (one_w _) ] ] => rewrite to_nat_one_w
           end; lia.

  Lemma V_const k i : V k (const_val i) (const_val i).
  Proof. destruct i. eapply (V_Vconstr cenv VT_cp); eauto. Qed.

  (** ** Constant parameters *)

  Lemma E_bind_consts (P : PostT) ex k p1 xs cs e2 rho2
        (Htgt : post_target_step P) :
    E P ex k p1 (e2, bind_env xs cs rho2) ->
    E P ex k p1 (bind_consts xs cs e2, rho2).
  Proof.
    revert cs rho2. induction xs as [| x xs IH]; intros cs rho2 HE.
    - destruct cs; eauto.
    - destruct cs as [| [[c w] |] cs]; simpl in *; eauto.
      eapply (E_add_constr cenv VT_cp); eauto.
  Qed.

  (** ** Compatibility lemmas for internal calls *)

  Lemma E_app_cp (P : PostT) ex k K rho1 rho2 f w ys cs
        (Hcompat : post_app_compat' f w ys rho1 f w (live_args ys (cmask cs)) rho2 P PG)
        (HOOT : post_OOT' (Eapp f w ys) rho1 (Eapp f w (live_args ys (cmask cs))) rho2 P) :
    exposedb w = false ->
    Lc ! w = Some cs ->
    K_inv K rho1 ->
    const_ok K ys cs ->
    wf_env rho1 ->
    var_rel k rho1 rho2 f f ->
    Forall2 (var_rel k rho1 rho2) (live_args ys (cmask cs)) (live_args ys (cmask cs)) ->
    E P ex k (Eapp f w ys, rho1) (Eapp f w (live_args ys (cmask cs)), rho2).
  Proof.
    intros Hw HL HK Hok Hwf Hfun Hall r1 cin cout Hleq Hstep. inv Hstep.
    - exists OOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H.
      edestruct Hfun as (v2 & Hget2 & Hv); eauto.
      eapply (V_internal_fun cenv VT_cp) in Hv;
        [| rewrite exposed_val_Vfun; intros (w' & xs' & e' & Hfn' & Hw'); congruence ].
      destruct v2; try contradiction.
      edestruct var_rel_get_list as (vs2 & Hgetl2 & Hvs); [ eassumption | eapply live_args_get_list; eauto |].
      edestruct (Hv vs vs2 (k - 1)) as (cs' & e2 & HL' & Hf2 & Hbody); eauto.
      rewrite HL in HL'. inv HL'.
      edestruct Hbody as (rho2' & Hset2 & Hb). { symmetry. eapply Forall2_length; eauto. }
      edestruct Hb as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
        [ fuel_arith | eapply wf_env_get_list; eauto | eapply const_ok_vals; eauto | | | eassumption | ].
      + eapply (V_mono_Forall2 cenv VT_cp); eauto. lia.
      + fuel_arith.
      + do 3 eexists. split; [| split ].
        * econstructor 2; [ econstructor; eauto |].
          -- congruence.
          -- eapply (R_exposed_ex cenv VT_cp); eauto.
        * eapply Hcompat; eauto.
        * eapply (R_mono cenv VT_cp); eauto. fuel_arith.
  Qed.

  Lemma E_letapp_cp (P : PostT) ex k K rho1 rho2 x f w ys cs e1 e2
        (Hcompat : post_letapp_compat' cenv x f w ys e1 rho1 x f w (live_args ys (cmask cs)) e2 rho2 P P PG)
        (HcompatOOT : post_letapp_compat_OOT' x f w ys e1 rho1 x f w (live_args ys (cmask cs)) e2 rho2 P PG)
        (HOOT : post_OOT' (Eletapp x f w ys e1) rho1 (Eletapp x f w (live_args ys (cmask cs)) e2) rho2 P) :
    exposedb w = false ->
    Lc ! w = Some cs ->
    K_inv K rho1 ->
    const_ok K ys cs ->
    wf_env rho1 ->
    var_rel k rho1 rho2 f f ->
    Forall2 (var_rel k rho1 rho2) (live_args ys (cmask cs)) (live_args ys (cmask cs)) ->
    (forall m v1 v2,
        m < k ->
        V m v1 v2 ->
        E P ex m (e1, M.set x v1 rho1) (e2, M.set x v2 rho2)) ->
    E P ex k (Eletapp x f w ys e1, rho1) (Eletapp x f w (live_args ys (cmask cs)) e2, rho2).
  Proof.
    intros Hw HL HK Hok Hwf Hfun Hall Hk r1 cin cout Hleq Hstep. inv Hstep.
    - exists OOT, cin, <0>. split; [ constructor; eassumption |].
      split; [ eapply HOOT; eassumption | exact I ].
    - inv H;
        (edestruct Hfun as (v2 & Hget2 & Hv); eauto;
         eapply (V_internal_fun cenv VT_cp) in Hv;
         [| rewrite exposed_val_Vfun; intros (w' & xs' & e' & Hfn' & Hw'); congruence ];
         destruct v2; try contradiction;
         edestruct var_rel_get_list as (vs2 & Hgetl2 & Hvs);
         [ eassumption | eapply live_args_get_list; eauto |];
         edestruct (Hv vs vs2 (k - 1)) as (cs' & eb2 & HL' & Hf2 & Hbody); eauto;
         rewrite HL in HL'; inv HL';
         edestruct Hbody as (rho2' & Hset2 & Hb); [ symmetry; eapply Forall2_length; eauto |]).
      + edestruct Hb as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
          [ fuel_arith | eapply wf_env_get_list; eauto | eapply const_ok_vals; eauto | | | eassumption | ].
        * eapply (V_mono_Forall2 cenv VT_cp); eauto. lia.
        * fuel_arith.
        * destruct r2 as [| v2]; try contradiction. simpl in HR.
          edestruct (Hk (k - 1 - to_nat cin1)) as (r2 & cin'' & cout'' & Hstep3 & Hpost' & HR');
            [ fuel_arith | eassumption | | eassumption | ]; [ fuel_arith | ].
          do 3 eexists. split; [| split ].
          -- econstructor 2; [ econstructor; eauto |].
             ++ congruence.
             ++ eapply (R_exposed_ex cenv VT_cp); eauto.
          -- eapply Hcompat; eauto.
          -- eapply (R_mono cenv VT_cp); eauto. fuel_arith.
      + edestruct Hb as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
          [ fuel_arith | eapply wf_env_get_list; eauto | eapply const_ok_vals; eauto | | | eassumption | ].
        * eapply (V_mono_Forall2 cenv VT_cp); eauto. lia.
        * fuel_arith.
        * destruct r2; try contradiction.
          do 3 eexists. split; [| split ].
          -- econstructor 2; [ eapply BStept_letapp_oot; eauto; congruence |].
             intros; exact I.
          -- eapply HcompatOOT; eauto.
          -- exact I.
  Qed.

  (** ** Postconditions *)

  Context (P : nat -> PostT) {Hdead : Post_dead cenv P PG Gb}
          (Htgt : post_target_step (P Gb)).

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
    forall m n K ex e e' rho1 rho2,
      m < k ->
      n <= Gb ->
      trans Lc Gb K n e e' ->
      K_inv K rho1 ->
      G m (occurs_free e') rho1 rho2 ->
      E (P n) ex m (e, rho1) (e', rho2).

  Lemma Vfun_cp k K rho1 rho2 B B' :
    trans_fundefs Lc Gb K B B' ->
    IH_exp k ->
    K_inv K (def_funs B B rho1 rho1) ->
    G k (occurs_free_fundefs B') rho1 rho2 ->
    forall f, name_in_fundefs B f -> V k (Vfun rho1 B f) (Vfun rho2 B' f).
  Proof.
    intros HB. induction k as [k IHk] using lt_wf_rec. intros Hexp HK HG f Hin.
    assert (Hdefs : forall j, j < k -> forall g, name_in_fundefs B g ->
                                      V j (Vfun rho1 B g) (Vfun rho2 B' g)).
    { intros j Hlt g Hg. eapply IHk; eauto.
      - intros m n K' ex e e' r1 r2 Hm. eapply Hexp. lia.
      - eapply (G_mono cenv VT_cp); eauto. lia. }
    assert (Henv : forall j xs vs1 vs2 rho1' rho2' S,
               j < k ->
               S \subset FromList xs :|: (name_in_fundefs B' :|: occurs_free_fundefs B') ->
               Forall2 (V j) vs1 vs2 ->
               set_lists xs vs1 (def_funs B B rho1 rho1) = Some rho1' ->
               set_lists xs vs2 (def_funs B' B' rho2 rho2) = Some rho2' ->
               G j S rho1' rho2').
    { intros j xs vs1 vs2 rho1' rho2' S Hlt HS Hvs Hs1 Hs2.
      eapply (G_set_lists cenv VT_cp); eauto.
      eapply (G_def_funs cenv VT_cp); try (now apply HG).
      - eapply (G_antimon cenv VT_cp). eapply (G_mono cenv VT_cp); eauto. lia.
        intros z Hz. inv Hz. inv H. eapply HS in H1. inv H1; [ exfalso; eauto |].
        inv H; eauto. exfalso. eapply H0. eapply trans_fundefs_names; eauto.
      - eapply trans_fundefs_names; eauto.
      - intros g Hg. eapply Hdefs; eauto. }
    edestruct name_in_fundefs_find_def as (w & xs & e & Hfind); eauto.
    edestruct trans_fundefs_find_def as
        (e' & [ (Hw & Htrans & Hfind') | (cs & Hw & HL & Hlen & Hnd & Htrans & Hfind') ]); eauto.
    - (* exposed function: unchanged calling convention *)
      eapply (V_Vfun_exposed cenv VT_cp); eauto; try now apply HG.
      eapply (V_fun_def cenv VT_cp); eauto.
      intros j vs1 vs2 rho1' rho2' Hlt Hexpv Hvs Hs1 Hs2.
      eapply (E_post_mono cenv VT_cp); [ exact P_PG |].
      eapply Hexp; eauto.
      + eapply K_inv_set_lists; eauto. destruct vs1; exact I.
      + eapply Henv; eauto. eapply occurs_free_in_fun; eauto.
    - (* internal function: constant parameters bound on entry *)
      eapply (V_Vfun_internal cenv VT_cp); try now apply HG.
      + constructor. apply HG.
      + rewrite exposed_val_Vfun. intros (w' & xs' & e'' & Hfn' & Hw'). congruence.
      + rewrite exposed_val_Vfun. intros (w' & xs' & e'' & Hfn' & Hw'). congruence.
      + unfold VT_cp; cbn -[E']. intros vs1 vs2 j w' xs1 e1 rho1' Hf1 Hs1.
        rewrite Hfind in Hf1. inv Hf1.
        exists cs, (bind_consts xs1 cs e'). split; [ eassumption | split; [ eassumption |] ].
        intros Hlen2.
        edestruct (set_lists_length3 (def_funs B' B' rho2 rho2) (live_args xs1 (cmask cs)) vs2) as [rho2' Hs2].
        { rewrite Hlen2. eapply live_args_length. eapply set_lists_length_eq. symmetry. eassumption. }
        eexists; split; [ symmetry; eassumption |].
        intros Hlt Hwf Hc Hvs.
        eapply (E_post_mono cenv VT_cp); [ exact P_PG |].
        eapply E_bind_consts; [ exact Htgt |].
        eapply Hexp; eauto.
        * eapply K_inv_set_lists; [ eassumption | eassumption | symmetry; eassumption ].
        * eapply Henv with (vs2 := pad_consts cs vs2); [ eassumption | | | symmetry; eassumption | ].
          -- intros z Hz. destruct (in_dec peq z xs1) as [Hin' | Hnin]; [ now left |].
             edestruct (occurs_free_in_fun _ _ _ _ _ Hfind' z) as [z' Hz' | z' Hz'];
               [ eapply occurs_free_bind_consts_r; eauto | | now right ].
             exfalso. eapply Hnin. eapply live_args_In; eauto.
          -- eapply Forall2_pad_consts; eauto.
             ++ rewrite Hlen. symmetry. eapply set_lists_length_eq. symmetry. eassumption.
             ++ intros. eapply V_const.
          -- eapply bind_env_set_lists; eauto.
  Qed.

  (** ** Fundamental property *)

  Ltac solve_K :=
    first [ eassumption
          | eapply K_inv_remove; eassumption
          | eapply K_inv_def_funs; eassumption
          | exact (K_inv_set _ _ _ _ ltac:(eassumption)) ].

  Ltac solve_G_set :=
    eapply (G_set cenv VT_cp); eauto; eapply (G_antimon cenv VT_cp);
    [ eapply (G_mono cenv VT_cp); eauto; lia | normalize_occurs_free; sets ].

  Lemma fundamental k n K ex e e' rho1 rho2 :
    n <= Gb ->
    trans Lc Gb K n e e' ->
    K_inv K rho1 ->
    G k (occurs_free e') rho1 rho2 ->
    E (P n) ex k (e, rho1) (e', rho2).
  Proof.
    revert n K ex e e' rho1 rho2.
    induction k as [k IH] using lt_wf_rec.
    assert (IH' : IH_exp k) by (intros m n K ex e e' r1 r2 Hlt; eapply IH; eauto).
    intros n K ex e e' rho1 rho2 HnG Htrans. revert ex rho1 rho2 HnG.
    induction Htrans; intros ex rho1 rho2 HnG HK HG;
      pose proof (Hprops_n _ HnG) as Hprops'; destruct Hprops'.
    - (* Econstr, constant *)
      eapply (E_constr_compat_vals cenv VT_cp); eauto.
      intros m vs1 v2 Hlt Hget Hv. simpl in Hget. inv Hget.
      eapply IH; [ lia | exact HnG | eassumption | solve_K | solve_G_set ].
    - (* Econstr *)
      eapply (E_constr_compat cenv VT_cp); eauto.
      + eapply (G_Forall2_var_rel cenv VT_cp); eauto. normalize_occurs_free. sets.
      + intros m v1 v2 Hlt Hv.
        eapply IH; [ lia | exact HnG | eassumption | solve_K | solve_G_set ].
    - (* Eproj *)
      eapply (E_proj_compat cenv VT_cp); eauto.
      + eapply (G_var_rel cenv VT_cp); eauto. fv_mem.
      + intros m v1 v2 Hlt Hv.
        eapply IH; [ lia | exact HnG | eassumption | solve_K | solve_G_set ].
    - (* Ecase [] *)
      eapply (E_case_nil_compat cenv VT_cp); eauto.
    - (* Ecase (_ :: _) *)
      eapply (E_case_cons_compat cenv VT_cp); eauto.
      + eapply trans_case_tags; eauto.
      + eapply (G_var_rel cenv VT_cp); eauto. fv_mem.
      + intros m Hlt. eapply IH; [ lia | exact HnG | eassumption | solve_K |].
        eapply (G_antimon cenv VT_cp). eapply (G_mono cenv VT_cp); eauto. lia.
        normalize_occurs_free. sets.
      + eapply IHHtrans2; eauto.
        eapply (G_antimon cenv VT_cp); eauto. normalize_occurs_free. sets.
    - (* Eletapp, exposed *)
      eapply (E_letapp_compat cenv VT_cp); eauto.
      + eapply (var_rel_exposed_fun cenv VT_cp); eauto. eapply (G_var_rel cenv VT_cp); eauto. fv_mem.
      + eapply (G_Forall2_var_rel cenv VT_cp); eauto. normalize_occurs_free. sets.
      + intros m v1 v2 Hlt _ Hv.
        eapply IH; [ lia | exact HnG | eassumption | solve_K | solve_G_set ].
    - (* Eletapp, internal *)
      eapply E_letapp_cp; eauto.
      + eapply HG.
      + eapply (G_var_rel cenv VT_cp); eauto. fv_mem.
      + eapply (G_Forall2_var_rel cenv VT_cp); eauto. normalize_occurs_free. sets.
      + intros m v1 v2 Hlt Hv.
        eapply IH; [ lia | exact HnG | eassumption | solve_K | solve_G_set ].
    - (* Eapp, exposed *)
      eapply (E_app_compat cenv VT_cp); eauto.
      + eapply (var_rel_exposed_fun cenv VT_cp); eauto. eapply (G_var_rel cenv VT_cp); eauto. fv_mem.
      + eapply (G_Forall2_var_rel cenv VT_cp); eauto. normalize_occurs_free. sets.
    - (* Eapp, internal *)
      eapply E_app_cp; eauto.
      + eapply HG.
      + eapply (G_var_rel cenv VT_cp); eauto. fv_mem.
      + eapply (G_Forall2_var_rel cenv VT_cp); eauto. normalize_occurs_free. sets.
    - (* Efun *)
      eapply (E_fun_compat cenv VT_cp); eauto.
      eapply (E_mono cenv VT_cp) with (k := k); [| lia ].
      eapply IHHtrans; [ exact HnG | solve_K |].
      eapply (G_antimon cenv VT_cp); [| eapply occurs_free_Efun_Included ].
      eapply (G_def_funs cenv VT_cp).
      + eapply (G_antimon cenv VT_cp); eauto.
        intros z [Hz Hn]. destruct Hz as [z Hz | z Hz]; [ exact Hz |].
        exfalso; apply Hn.
        match goal with
        | [ HB : trans_fundefs _ _ _ _ _ |- _ ] => apply (proj2 (trans_fundefs_names _ _ _ _ _ HB z)); exact Hz
        end.
      + eapply HG.
      + eapply HG.
      + eapply trans_fundefs_names; eauto.
      + intros f Hfn. eapply Vfun_cp; eauto.
        * eapply K_inv_def_funs; eauto.
        * eapply (G_antimon cenv VT_cp); eauto. eapply occurs_free_fundefs_Efun_Included.
    - (* Eprim_val *)
      eapply (E_stuck_compat cenv VT_cp); eauto. intros. eapply Eprim_val_stuck.
    - (* Eprim *)
      eapply (E_stuck_compat cenv VT_cp); eauto. intros. eapply Eprim_stuck.
    - (* Ehalt *)
      eapply (E_halt_compat cenv VT_cp); eauto.
      eapply (G_var_rel cenv VT_cp); eauto. fv_mem.
    - (* dead constant *)
      eapply (E_post_mono cenv VT_cp); [ eapply (P_mono (S n)); lia |].
      eapply (E_dead_constr cenv VT_cp); [ eapply P_src; lia | eapply P_OOT; lia | eapply HG |].
      intros vs Hget Hv. simpl in Hget. inv Hget.
      eapply IHHtrans; [ lia | solve_K |]. eapply (G_set_l_not_in cenv VT_cp); eauto.
    - (* dead Econstr *)
      eapply (E_post_mono cenv VT_cp); [ eapply (P_mono (S n)); lia |].
      eapply (E_dead_constr cenv VT_cp); [ eapply P_src; lia | eapply P_OOT; lia | eapply HG |].
      intros vs _ Hv. eapply IHHtrans; [ lia | solve_K |]. eapply (G_set_l_not_in cenv VT_cp); eauto.
    - (* dead Eproj *)
      eapply (E_post_mono cenv VT_cp); [ eapply (P_mono (S n)); lia |].
      eapply (E_dead_proj cenv VT_cp); [ eapply P_src; lia | eapply P_OOT; lia | eapply HG |].
      intros v Hv. eapply IHHtrans; [ lia | solve_K |]. eapply (G_set_l_not_in cenv VT_cp); eauto.
    - (* dead Efun *)
      eapply (E_post_mono cenv VT_cp); [ eapply (P_mono (S n)); lia |].
      eapply (E_dead_fun cenv VT_cp); [ eapply P_src; lia | eapply P_OOT; lia |].
      eapply IHHtrans; [ lia | solve_K |]. eapply (G_def_funs_l_not_in cenv VT_cp); eauto. eapply HG.
  Qed.

  (** ** Top level *)

  Lemma E_top_cp n e e' :
    n <= Gb -> trans Lc Gb (M.empty _) n e e' -> E_top cenv VT_cp (P n) PG e e'.
  Proof.
    intros Hn Htrans k rho1 rho2 [HG _] Hbind. eapply fundamental; eauto.
    - eapply K_inv_empty.
    - eapply (G_antimon cenv VT_cp); eauto. eapply trans_occurs_free; eauto.
  Qed.

  (** Constant propagation, with local constants and dead-binding
      elimination, is in the λweb relation. *)
  Theorem E_web_cp n e e' :
    n <= Gb -> trans Lc Gb (M.empty _) n e e' -> E_web cenv (P n) PG e e'.
  Proof.
    intros Hn Htrans. exact (E_top_E_web cenv VT_cp (P n) PG e e' (E_top_cp n e e' Hn Htrans)).
  Qed.

End CP_rel.

(** * Refinement, with divergence preservation *)

Section CP_top.

  Variables (cenv : term.ctor_env) (Lc : M.t (list (option const_info))) (Gb : nat).

  Theorem cp_refines n e e' :
    closed_exp e -> n <= Gb -> trans Lc Gb (M.empty _) n e e' -> refines cenv value_ref e e'.
  Proof.
    intros Hc Hn Htr.
    eapply (E_web_refines cenv (dead_bound n Gb) (dead_bound Gb Gb) (dead_bound_upper_bound n Gb)); eauto.
    eapply (E_web_cp cenv Lc Gb (dead_bound Gb Gb) (fun n => dead_bound n Gb)); eauto.
    eapply dead_bound_target_step.
  Qed.

End CP_top.
