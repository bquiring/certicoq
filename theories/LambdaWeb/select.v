(* Transforming a subset of the webs.

   A web transformation need not transform every internal web: [sel w]
   says whether web [w] is transformed.  The closures of the other internal
   webs keep their calling convention, and are related like those of
   exposed webs, by [V_fun].  [VT_sel sel VT] is the transformation-specific
   relation that uses [VT] for the closures of selected webs, and [V_fun]
   for the others.  A function or call of web [w] is then left unchanged
   when [keeps sel w] (exposed or not selected), and handled by the
   generic compatibility lemmas. *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics algebra.
From CertiRocq.LambdaANF Require term term_util.
From CertiRocq.LambdaWeb Require Import syntax semantics exposed post compat.

Import ListNotations.

Open Scope alg_scope.

(** Functions and calls of web [w] keep their calling convention *)
Definition keeps (sel : web -> bool) (w : web) : bool := exposedb w || negb (sel w).

Lemma keeps_internal sel w : keeps sel w = false <-> exposedb w = false /\ sel w = true.
Proof. unfold keeps. destruct (exposedb w), (sel w); simpl; intuition congruence. Qed.

Section Select.

  Variable (cenv : term.ctor_env).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Local Notation PostT := (@exposed.PostT fuel trace).
  Local Notation PostGT := (@exposed.PostGT fuel trace).
  Local Notation VTransT := (@exposed.VTransT fuel trace).

  Variable (sel : web -> bool).

  Definition VT_sel (VT : VTransT) : VTransT :=
    fun PG V' k v1 v2 =>
      match val_web v1 with
      | Some w => if sel w then VT PG V' k v1 v2 else V_fun cenv PG V' k v1 v2
      | None => VT PG V' k v1 v2
      end.

  Global Instance VTransProps_sel VT {HVT : VTransProps VT} : VTransProps (VT_sel VT).
  Proof.
    constructor; unfold VT_sel.
    - intros PG V1 V2 k v1 v2 Hext.
      destruct (val_web v1) as [w |]; [ destruct (sel w) |].
      + eapply VT_ext; eauto.
      + eapply V_fun_ext. intros. eapply Hext; eauto.
      + eapply VT_ext; eauto.
    - intros PG V k j v1 v2 Hmono.
      destruct (val_web v1) as [w |]; [ destruct (sel w) |].
      + eapply VT_mono; eauto.
      + eapply V_fun_mono.
      + eapply VT_mono; eauto.
  Qed.

  Context (VT : VTransT) {HVT : VTransProps VT} (PG : PostGT).

  Notation VS := (VT_sel VT).
  Notation V := (V cenv VS PG).

  Lemma fun_web_find_def B f w xs e : find_def f B = Some (w, xs, e) -> fun_web B f = Some w.
  Proof. unfold fun_web. intros H; rewrite H; reflexivity. Qed.

  Lemma not_exposed_Vfun rho B f w xs e :
    find_def f B = Some (w, xs, e) -> exposedb w = false -> ~ exposed_val (Vfun rho B f).
  Proof. rewrite exposed_val_Vfun. intros H Hw0 (w' & xs' & e' & H' & Hw'). congruence. Qed.

  (** ** Closures that keep their calling convention *)

  Lemma V_keeps_fun k rho1 B1 f1 v2 w :
    V k (Vfun rho1 B1 f1) v2 ->
    fun_web B1 f1 = Some w ->
    keeps sel w = true ->
    V_fun cenv PG V k (Vfun rho1 B1 f1) v2.
  Proof.
    intros Hv Hweb Hk. unfold keeps in Hk.
    destruct (exposedb w) eqn:Hw; [ eapply (V_exposed_fun cenv VS); eauto |].
    simpl in Hk. destruct (sel w) eqn:Hs; try discriminate.
    eapply (V_internal_fun cenv VS) in Hv.
    - unfold VT_sel in Hv. simpl in Hv. rewrite Hweb, Hs in Hv. exact Hv.
    - rewrite exposed_val_Vfun. intros (w' & xs' & e' & Hfd & Hw').
      unfold fun_web in Hweb. rewrite Hfd in Hweb. inv Hweb. congruence.
  Qed.

  Lemma var_rel_keeps_fun k rho1 rho2 f1 f2 w :
    keeps sel w = true -> var_rel cenv VS PG k rho1 rho2 f1 f2 -> fun_rel cenv VS PG k rho1 rho2 f1 f2 w.
  Proof.
    intros Hk Hvar v1 Hget. edestruct Hvar as (v2 & Hget2 & Hv); eauto.
    eexists; split; eauto. intros Hweb. destruct v1; simpl in Hweb; try congruence.
    eapply V_keeps_fun; eauto.
  Qed.

  Lemma V_Vfun_keeps k rho1 B1 f1 rho2 B2 f2 w xs1 e1 xs2 e2 :
    wf_env rho1 -> wf_env rho2 ->
    find_def f1 B1 = Some (w, xs1, e1) ->
    find_def f2 B2 = Some (w, xs2, e2) ->
    keeps sel w = true ->
    V_fun cenv PG V k (Vfun rho1 B1 f1) (Vfun rho2 B2 f2) ->
    V k (Vfun rho1 B1 f1) (Vfun rho2 B2 f2).
  Proof.
    intros Hwf1 Hwf2 Hf1 Hf2 Hk Hfun. unfold keeps in Hk.
    destruct (exposedb w) eqn:Hw; [ eapply (V_Vfun_exposed cenv VS); eauto |].
    simpl in Hk. destruct (sel w) eqn:Hs; try discriminate.
    eapply (V_Vfun_internal cenv VS); eauto.
    - constructor; eauto.
    - eapply not_exposed_Vfun; eauto.
    - eapply not_exposed_Vfun; eauto.
    - unfold VT_sel. simpl. erewrite fun_web_find_def by eassumption. rewrite Hs. exact Hfun.
  Qed.

  (** ** Closures of selected webs *)

  Lemma V_sel_internal k rho1 B1 f1 v2 w xs e :
    V k (Vfun rho1 B1 f1) v2 ->
    find_def f1 B1 = Some (w, xs, e) ->
    exposedb w = false -> sel w = true ->
    VT PG V k (Vfun rho1 B1 f1) v2.
  Proof.
    intros Hv Hfd Hw Hs. eapply (V_internal_fun cenv VS) in Hv; [| eapply not_exposed_Vfun; eauto ].
    unfold VT_sel in Hv. simpl in Hv. erewrite fun_web_find_def in Hv by eassumption.
    rewrite Hs in Hv. exact Hv.
  Qed.

  Lemma V_Vfun_sel k rho1 B1 f1 v2 w xs e :
    wf_env rho1 -> wf_val v2 -> ~ exposed_val v2 ->
    find_def f1 B1 = Some (w, xs, e) ->
    exposedb w = false -> sel w = true ->
    VT PG V k (Vfun rho1 B1 f1) v2 ->
    V k (Vfun rho1 B1 f1) v2.
  Proof.
    intros Hwf1 Hwf2 Hn2 Hfd Hw Hs Hvt.
    eapply (V_Vfun_internal cenv VS); eauto.
    - eapply not_exposed_Vfun; eauto.
    - unfold VT_sel. simpl. erewrite fun_web_find_def by eassumption. rewrite Hs. exact Hvt.
  Qed.

End Select.
