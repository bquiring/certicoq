(* Flow-directed arity raising (argument flattening) on λweb, for
   CertiRocq's λANF.

   A map [La] assigns to every transformed (internal) web a list with one
   entry per parameter: [Some (wc, n, c)] when every call passes, at that
   position, a constructor of web [wc] with tag [c] and [n] fields, [None]
   otherwise.  Calls of the web project the fields of the flattened
   arguments into fresh variables and pass them instead; functions of the
   web take the fields as parameters and rebuild the constructor on entry:

     f x y = e                    ~>   f x y1 .. yn = let y = C(y1, .., yn) in e
     ... f a b ...                ~>   ... let z1 = b.0 in .. let zn = b.(n-1) in f a z1 .. zn ...

   Shapes are found locally: the relation carries a scoped environment [K]
   of the variables known to hold a constructor of a given web, tag and
   arity (bound by [Econstr], or flattened parameters of the enclosing
   function), and flattened arguments of calls must be such variables.

   The target takes extra steps (the projections and the rebuilds), which
   the postcondition absorbs ([post_target_step]). *)

From Stdlib Require Import NArith.BinNat ZArith.ZArith Lists.List Sets.Ensembles Bool
     micromega.Lia Relations.Relations.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import Ensembles_util List_util tactics algebra set_util.
From CertiRocq.LambdaANF Require term term_util.
From CertiRocq.LambdaWeb Require Import syntax semantics exposed post compat dead select indep comp bound dpe.

Import ListNotations.

Open Scope alg_scope.

(** * Shapes *)

(** A constructor of web [wc], with [n] fields and tag [c] *)
Definition shape : Type := web * nat * ctor_tag.

Definition shaped (s : option shape) (v : val) : Prop :=
  match s with
  | Some (wc, n, c) => exists us, v = Vconstr wc c us /\ length us = n
  | None => True
  end.

(** Flattened constructors are internal: rebuilding an exposed constructor
    would need its fields to be exposed. *)
Definition info_ok (s : option shape) : Prop :=
  match s with Some (wc, _, _) => exposedb wc = false | None => True end.

(** Flattened constructors have fields (nullary ones are constants, see cp.v) *)
Definition pos_ok (s : option shape) : Prop :=
  match s with Some (_, n, _) => 0 < n | None => True end.

(** The fresh names of the fields of a position *)
Definition fresh_ok (s : option shape) (ys : list var) : Prop :=
  match s with Some (_, n, _) => length ys = n | None => ys = [] end.

(** Replace each flattened parameter (or argument) by the names of its fields *)
Fixpoint flat_vars (xs : list var) (ss : list (option shape)) (yss : list (list var)) : list var :=
  match xs, ss, yss with
  | x :: xs', None :: ss', _ :: yss' => x :: flat_vars xs' ss' yss'
  | _ :: xs', Some _ :: ss', ys :: yss' => ys ++ flat_vars xs' ss' yss'
  | _, _, _ => []
  end.

(** Replace each flattened value by its fields *)
Fixpoint flat_vals (vs : list val) (ss : list (option shape)) : list val :=
  match vs, ss with
  | v :: vs', None :: ss' => v :: flat_vals vs' ss'
  | v :: vs', Some _ :: ss' =>
      match v with Vconstr _ _ us => us | _ => [] end ++ flat_vals vs' ss'
  | _, _ => []
  end.

(** Project the fields [i], [i+1], ... of [y] into [zs] *)
Fixpoint proj_fields (y : var) (wc : web) (c : ctor_tag) (i : nat) (zs : list var) (k : exp) : exp :=
  match zs with
  | [] => k
  | z :: zs' => Eproj z wc c (N.of_nat i) y (proj_fields y wc c (S i) zs' k)
  end.

(** Project the fields of every flattened argument *)
Fixpoint proj_args (ys : list var) (ss : list (option shape)) (zss : list (list var)) (k : exp) : exp :=
  match ys, ss, zss with
  | y :: ys', Some (wc, _, c) :: ss', zs :: zss' => proj_fields y wc c 0 zs (proj_args ys' ss' zss' k)
  | _ :: ys', None :: ss', _ :: zss' => proj_args ys' ss' zss' k
  | _, _, _ => k
  end.

(** Rebuild every flattened parameter from its fields *)
Fixpoint rebuild (xs : list var) (ss : list (option shape)) (yss : list (list var)) (e : exp) : exp :=
  match xs, ss, yss with
  | x :: xs', Some (wc, _, c) :: ss', ys :: yss' => Econstr x wc c ys (rebuild xs' ss' yss' e)
  | _ :: xs', None :: ss', _ :: yss' => rebuild xs' ss' yss' e
  | _, _, _ => e
  end.

(** ** The environment of shapes *)

(** Flattened arguments are variables of known shape *)
Fixpoint shape_ok (K : M.t shape) (ys : list var) (ss : list (option shape)) : Prop :=
  match ys, ss with
  | y :: ys', Some s :: ss' => K ! y = Some s /\ shape_ok K ys' ss'
  | _ :: ys', None :: ss' => shape_ok K ys' ss'
  | _, _ => True
  end.

(** The shapes of the parameters *)
Fixpoint param_shapes (xs : list var) (ss : list (option shape)) (K : M.t shape) : M.t shape :=
  match xs, ss with
  | x :: xs', Some s :: ss' => M.set x s (param_shapes xs' ss' K)
  | x :: xs', None :: ss' => M.remove x (param_shapes xs' ss' K)
  | x :: xs', [] => M.remove x (param_shapes xs' [] K)
  | [], _ => K
  end.

Fixpoint remove_names (B : fundefs) (K : M.t shape) : M.t shape :=
  match B with
  | Fcons f _ _ _ B' => M.remove f (remove_names B' K)
  | Fnil => K
  end.

(** The invariant of [K]: its variables hold constructors of their shape *)
Definition K_inv (K : M.t shape) (rho : env) :=
  forall x s, K ! x = Some s -> exists v, M.get x rho = Some v /\ shaped (Some s) v.

Lemma K_inv_empty rho : K_inv (M.empty _) rho.
Proof. intros x s H. rewrite M.gempty in H. congruence. Qed.

Lemma K_inv_set K rho x s v : K_inv K rho -> shaped (Some s) v -> K_inv (M.set x s K) (M.set x v rho).
Proof.
  intros HK Hv z s' Hz. destruct (peq z x); subst.
  - rewrite M.gss in *. inv Hz. eexists; split; eauto.
  - rewrite M.gso in *; eauto.
Qed.

Lemma K_inv_remove K rho x v : K_inv K rho -> K_inv (M.remove x K) (M.set x v rho).
Proof.
  intros HK z s Hz. destruct (peq z x); subst.
  - rewrite M.grs in *. congruence.
  - rewrite M.gro in Hz; eauto. rewrite M.gso; eauto.
Qed.

Lemma K_inv_set_lists K rho rho' xs vs ss :
  K_inv K rho -> Forall2 shaped ss vs \/ ss = [] -> set_lists xs vs rho = Some rho' ->
  K_inv (param_shapes xs ss K) rho'.
Proof.
  revert vs ss rho'. induction xs as [| x xs IH]; intros vs ss rho' HK Hss Hs.
  - destruct vs; simpl in Hs; inv Hs. destruct ss; eauto.
  - destruct vs as [| v vs]; simpl in Hs; try congruence.
    destruct (set_lists xs vs rho) as [rho'' |] eqn:Hs'; inv Hs.
    destruct Hss as [Hss | ->].
    + destruct ss as [| [s |] ss]; inv Hss; simpl in *.
      * eapply K_inv_set; eauto.
      * eapply K_inv_remove; eauto.
    + simpl. eapply K_inv_remove. eapply (IH vs []); eauto.
Qed.

Lemma K_inv_def_funs K rho B0 B rhoc :
  K_inv K rho -> K_inv (remove_names B K) (def_funs B0 B rhoc rho).
Proof. induction B; simpl; eauto. intros HK. eapply K_inv_remove; eauto. Qed.

Lemma shape_ok_vals K rho ys vs ss :
  K_inv K rho -> shape_ok K ys ss -> get_list ys rho = Some vs -> length ys = length ss ->
  Forall2 shaped ss vs.
Proof.
  revert vs ss. induction ys as [| y ys IH]; intros vs ss HK Hok Hget Hlen; simpl in *.
  - inv Hget. destruct ss; simpl in *; try congruence. constructor.
  - destruct (M.get y rho) eqn:Hy; try congruence.
    destruct (get_list ys rho) eqn:Hys; try congruence. inv Hget.
    destruct ss as [| [s |] ss]; simpl in *; try congruence; inv Hlen.
    + destruct Hok as [Hs Hok]. constructor; eauto.
      eapply HK in Hs. destruct Hs as (v' & Hv' & Hsh). congruence.
    + constructor; [ exact I | eauto ].
Qed.

(** * The relation *)

Section AR_spec.

  Variable (La : WM.t (list (option shape))).

  Inductive trans : M.t shape -> exp -> exp -> Prop :=
  | Trans_constr :
      forall K x w t ys e e',
        trans (M.set x (w, length ys, t) K) e e' ->
        trans K (Econstr x w t ys e) (Econstr x w t ys e')
  | Trans_proj :
      forall K x w t i y e e',
        trans (M.remove x K) e e' ->
        trans K (Eproj x w t i y e) (Eproj x w t i y e')
  | Trans_case_nil :
      forall K x w,
        trans K (Ecase x w []) (Ecase x w [])
  | Trans_case_cons :
      forall K x w c e e' cl cl',
        trans K e e' ->
        trans K (Ecase x w cl) (Ecase x w cl') ->
        trans K (Ecase x w ((c, e) :: cl)) (Ecase x w ((c, e') :: cl'))
  | Trans_letapp_exposed :
      forall K x f w ys e e',
        keeps (sel_L La) w = true ->
        trans (M.remove x K) e e' ->
        trans K (Eletapp x f w ys e) (Eletapp x f w ys e')
  | Trans_letapp :
      forall K x f w ys e e' ss zss,
        exposedb w = false ->
        WM.get w La = Some ss ->
        length ys = length ss ->
        shape_ok K ys ss ->
        Forall pos_ok ss ->
        Forall2 fresh_ok ss zss ->
        NoDup (concat zss) ->
        Disjoint _ (FromList (concat zss)) (f |: FromList ys) ->
        Disjoint _ (FromList (concat zss)) (occurs_free e' \\ [set x]) ->
        trans (M.remove x K) e e' ->
        trans K (Eletapp x f w ys e) (proj_args ys ss zss (Eletapp x f w (flat_vars ys ss zss) e'))
  | Trans_app_exposed :
      forall K f w ys,
        keeps (sel_L La) w = true ->
        trans K (Eapp f w ys) (Eapp f w ys)
  | Trans_app :
      forall K f w ys ss zss,
        exposedb w = false ->
        WM.get w La = Some ss ->
        length ys = length ss ->
        shape_ok K ys ss ->
        Forall pos_ok ss ->
        Forall2 fresh_ok ss zss ->
        NoDup (concat zss) ->
        Disjoint _ (FromList (concat zss)) (f |: FromList ys) ->
        trans K (Eapp f w ys) (proj_args ys ss zss (Eapp f w (flat_vars ys ss zss)))
  | Trans_fun :
      forall K B B' e e',
        trans_fundefs (remove_names B K) B B' ->
        trans (remove_names B K) e e' ->
        trans K (Efun B e) (Efun B' e')
  | Trans_prim_val :
      forall K x p e,
        trans K (Eprim_val x p e) (Eprim_val x p e)
  | Trans_prim :
      forall K x p ys e,
        trans K (Eprim x p ys e) (Eprim x p ys e)
  | Trans_halt :
      forall K x,
        trans K (Ehalt x) (Ehalt x)
  with trans_fundefs : M.t shape -> fundefs -> fundefs -> Prop :=
  | Trans_Fnil : forall K, trans_fundefs K Fnil Fnil
  | Trans_Fcons_exposed :
      forall K f w xs e e' B B',
        keeps (sel_L La) w = true ->
        trans (param_shapes xs [] K) e e' ->
        trans_fundefs K B B' ->
        trans_fundefs K (Fcons f w xs e B) (Fcons f w xs e' B')
  | Trans_Fcons :
      forall K f w xs e e' B B' ss yss,
        exposedb w = false ->
        WM.get w La = Some ss ->
        length ss = length xs ->
        Forall info_ok ss ->
        Forall2 fresh_ok ss yss ->
        NoDup (xs ++ concat yss) ->
        Disjoint _ (FromList (concat yss)) (occurs_free e') ->
        trans (param_shapes xs ss K) e e' ->
        trans_fundefs K B B' ->
        trans_fundefs K (Fcons f w xs e B) (Fcons f w (flat_vars xs ss yss) (rebuild xs ss yss e') B').

  Scheme trans_mut := Induction for trans Sort Prop
  with trans_fundefs_mut := Induction for trans_fundefs Sort Prop.

  Combined Scheme trans_mutind from trans_mut, trans_fundefs_mut.

  (** ** Syntactic invariants *)

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
      (keeps (sel_L La) w = true /\ trans (param_shapes xs [] K) e e' /\
       find_def f B' = Some (w, xs, e')) \/
      (exists ss yss, exposedb w = false /\ WM.get w La = Some ss /\ length ss = length xs /\
                      Forall info_ok ss /\ Forall2 fresh_ok ss yss /\ NoDup (xs ++ concat yss) /\
                      Disjoint _ (FromList (concat yss)) (occurs_free e') /\
                      trans (param_shapes xs ss K) e e' /\
                      find_def f B' = Some (w, flat_vars xs ss yss, rebuild xs ss yss e')).
  Proof.
    intros H; induction H; simpl; intros Hfn; try congruence;
      destruct (M.elt_eq f f0); subst; eauto.
    - inv Hfn. eexists; left; eauto.
    - inv Hfn. eexists; right. do 2 eexists; eauto 20.
  Qed.

  Lemma trans_case_tags K x w cl cl' :
    trans K (Ecase x w cl) (Ecase x w cl') -> Forall2 (fun p p' => fst p = fst p') cl cl'.
  Proof.
    revert cl'. induction cl as [| [c e] cl IH]; intros cl' H; inv H; constructor; eauto.
  Qed.

End AR_spec.

(** ** Free variables of the new forms *)

Lemma flat_vars_In xs ss yss z :
  List.In z (flat_vars xs ss yss) -> List.In z xs \/ List.In z (concat yss).
Proof.
  revert ss yss. induction xs as [| x xs IH]; intros ss yss Hz; [ destruct ss, yss; inv Hz |].
  destruct ss as [| [s |] ss], yss as [| ys yss]; simpl in *; try contradiction.
  - apply in_app_or in Hz as [Hz | Hz]; [ right; apply in_or_app; now left |].
    edestruct IH as [H | H]; eauto. right. apply in_or_app. now right.
  - destruct Hz as [-> | Hz]; [ now left; left |].
    edestruct IH as [H | H]; eauto. right. apply in_or_app. now right.
Qed.

Lemma occurs_free_proj_fields y wc c i zs k z :
  occurs_free (proj_fields y wc c i zs k) z -> z = y \/ (occurs_free k z /\ ~ List.In z zs).
Proof.
  revert i. induction zs as [| z0 zs IH]; intros i Hz; simpl in *; [ right; split; auto |].
  apply occurs_free_Eproj in Hz. destruct Hz as [z' Hz | z' [Hz Hn]]; [ inv Hz; now left |].
  edestruct IH as [H | [H1 H2]]; eauto. right. split; auto.
  intros [Hc | Hc]; [ subst; apply Hn; constructor | auto ].
Qed.

Lemma occurs_free_proj_args ys ss zss k z :
  length ys = length ss -> Forall2 fresh_ok ss zss ->
  occurs_free (proj_args ys ss zss k) z -> List.In z ys \/ (occurs_free k z /\ ~ List.In z (concat zss)).
Proof.
  revert ss zss. induction ys as [| y ys IH]; intros ss zss Hlen Hf Hz.
  - destruct ss; simpl in Hlen; try congruence. inv Hf. right. split; auto.
  - destruct ss as [| s ss]; simpl in Hlen; try congruence. inv Hlen.
    inv Hf. rename y0 into zs, l' into zss.
    destruct s as [[[wc n] c] |]; simpl in Hz.
    + apply occurs_free_proj_fields in Hz. destruct Hz as [-> | [Hz Hn]]; [ now left; left |].
      destruct (IH _ _ ltac:(eassumption) ltac:(eassumption) Hz) as [Hi | [Hi1 Hi2]]; [ now left; right |].
      right. split; auto. simpl. intros Hc. apply in_app_or in Hc as [Hc | Hc]; auto.
    + match goal with H : fresh_ok None _ |- _ => simpl in H; subst end.
      destruct (IH _ _ ltac:(eassumption) ltac:(eassumption) Hz) as [Hi | [Hi1 Hi2]]; [ now left; right |].
      right. split; auto.
Qed.

Lemma occurs_free_rebuild xs ss yss e z :
  length xs = length ss -> Forall2 fresh_ok ss yss ->
  occurs_free (rebuild xs ss yss e) z ->
  List.In z (concat yss) \/ (occurs_free e z /\ (List.In z xs -> List.In z (flat_vars xs ss yss))).
Proof.
  revert ss yss. induction xs as [| x xs IH]; intros ss yss Hlen Hf Hz.
  - destruct ss; simpl in Hlen; try congruence. inv Hf. right. split; [ exact Hz | intros [] ].
  - destruct ss as [| s ss]; simpl in Hlen; try congruence. inv Hlen.
    inv Hf. rename y into ys, l' into yss.
    destruct s as [[[wc n] c] |]; simpl in Hz |- *.
    + apply occurs_free_Econstr in Hz. destruct Hz as [z' Hz | z' [Hz Hn]];
        [ left; apply in_or_app; now left |].
      destruct (IH _ _ ltac:(eassumption) ltac:(eassumption) Hz) as [Hi | [Hi1 Hi2]];
        [ left; apply in_or_app; now right |].
      right. split; auto. intros [Hc | Hc]; [ subst; exfalso; apply Hn; constructor |].
      apply in_or_app. right. auto.
    + match goal with H : fresh_ok None _ |- _ => simpl in H; subst end.
      destruct (IH _ _ ltac:(eassumption) ltac:(eassumption) Hz) as [Hi | [Hi1 Hi2]]; [ now left |].
      right. split; auto. intros [Hc | Hc]; [ now left | right; auto ].
Qed.

Lemma flat_vars_concat xs ss yss z :
  length xs = length ss -> Forall2 fresh_ok ss yss ->
  List.In z (concat yss) -> List.In z (flat_vars xs ss yss).
Proof.
  revert ss yss. induction xs as [| x xs IH]; intros ss yss Hlen Hf Hz.
  - destruct ss; simpl in Hlen; try congruence. inv Hf. inv Hz.
  - destruct ss as [| s ss]; simpl in Hlen; try congruence. inv Hlen. inv Hf.
    simpl in Hz. apply in_app_or in Hz as [Hz | Hz].
    + destruct s as [[[wc n] c] |]; simpl.
      * apply in_or_app. now left.
      * match goal with H : fresh_ok None _ |- _ => simpl in H; subst end. inv Hz.
    + destruct s as [[[wc n] c] |]; simpl.
      * apply in_or_app. right. eauto.
      * right. eauto.
Qed.

Lemma FromList_flat_vars xs ss yss :
  FromList (flat_vars xs ss yss) \subset FromList xs :|: FromList (concat yss).
Proof.
  intros z Hz. unfold FromList, Ensembles.In in *.
  destruct (flat_vars_In _ _ _ _ Hz); [ now left | now right ].
Qed.

Section AR_fv.

  Variable (La : WM.t (list (option shape))).

  Lemma trans_occurs_free :
    (forall K e e', trans La K e e' -> occurs_free e' \subset occurs_free e) /\
    (forall K B B', trans_fundefs La K B B' -> occurs_free_fundefs B' \subset occurs_free_fundefs B).
  Proof.
    apply trans_mutind; intros; normalize_occurs_free.
    all: repeat match goal with
                | [ Ht : trans_fundefs _ _ ?B ?B' |- context[name_in_fundefs ?B'] ] =>
                    rewrite <- (trans_fundefs_names_eq _ _ _ _ Ht)
                end.
    all: try solve [ sets ].
    - (* Eletapp, internal *)
      intros z Hz. edestruct occurs_free_proj_args as [Hy | [Hk Hn]]; [ eassumption | eassumption | exact Hz | |].
      + left. now right.
      + apply occurs_free_Eletapp in Hk. destruct Hk as [z' Hk | z' [Hk Hx]].
        * destruct Hk as [z' Hk | z' Hk]; [ left; now left |].
          apply FromList_flat_vars in Hk. destruct Hk as [z' Hk | z' Hk]; [ left; now right | contradiction ].
        * right. constructor; [ eauto | exact Hx ].
    - (* Eapp, internal *)
      intros z Hz. edestruct occurs_free_proj_args as [Hy | [Hk Hn]]; [ eassumption | eassumption | exact Hz | |].
      + now left.
      + apply occurs_free_Eapp in Hk. destruct Hk as [z' Hk | z' Hk]; [| now right ].
        apply FromList_flat_vars in Hk. destruct Hk as [z' Hk | z' Hk]; [ now left | contradiction ].
    - (* Fcons, internal *)
      eapply Included_Union_compat; [| eapply Included_Setminus_compat; [ eassumption | reflexivity ] ].
      intros z [Hz Hn].
      assert (Hlen' : length xs = length ss) by congruence.
      edestruct occurs_free_rebuild as [Hy | [Hfv Hin]]; [ exact Hlen' | eassumption | exact Hz | |].
      + exfalso. apply Hn. right. left. eapply flat_vars_concat; eauto.
      + constructor; [ eauto |].
        intros Hc. apply Hn. destruct Hc as [z' Hc | z' Hc]; [ now left |].
        destruct Hc as [z' Hc | z' Hc]; [| now right; right ].
        right. left. eapply Hin. exact Hc.
  Qed.

End AR_fv.

Lemma nthN_of_nat {A} (l : list A) i : nthN l (N.of_nat i) = nth_error l i.
Proof.
  revert i. induction l as [| a l IH]; intros i.
  - destruct i; reflexivity.
  - destruct i as [| i]; [ reflexivity |].
    rewrite nthN_equation. simpl.
    destruct (Pos.of_succ_nat i) eqn:Hp; rewrite <- IH; f_equal; lia.
Qed.

Lemma NoDup_app_split {A} (l1 l2 : list A) :
  NoDup (l1 ++ l2) -> NoDup l1 /\ NoDup l2 /\ (forall x, List.In x l1 -> ~ List.In x l2).
Proof.
  induction l1 as [| a l1 IH]; simpl; intros H.
  - split; [ constructor | split; [ exact H | intros _ [] ] ].
  - inversion H as [| a' l' Hnin Hnd Heq]; subst.
    destruct (IH Hnd) as (Hn1 & Hn2 & Hn3). split; [| split; [ exact Hn2 |] ].
    + constructor; [ intros Hc; apply Hnin; apply in_or_app; now left | exact Hn1 ].
    + intros x [-> | Hx]; [| eauto ]. intros Hc. apply Hnin. apply in_or_app. now right.
Qed.

Lemma skipn_nth_error {A} (l : list A) i v :
  nth_error l i = Some v -> skipn i l = v :: skipn (S i) l.
Proof.
  revert l. induction i as [| i IH]; intros [| a l] H; simpl in *; try congruence.
  - inv H. reflexivity.
  - eapply IH. exact H.
Qed.

Lemma get_list_app_inv {A} (l1 l2 : list var) (rho : M.t A) vs :
  get_list (l1 ++ l2) rho = Some vs ->
  exists vs1 vs2, vs = vs1 ++ vs2 /\ get_list l1 rho = Some vs1 /\ get_list l2 rho = Some vs2.
Proof.
  revert vs. induction l1 as [| x l1 IH]; intros vs H; simpl in *.
  - exists [], vs. eauto.
  - destruct (M.get x rho) as [v |]; try congruence.
    destruct (get_list (l1 ++ l2) rho) as [vs' |] eqn:H'; try congruence. inv H.
    destruct (IH vs' eq_refl) as (vs1 & vs2 & -> & H1 & H2).
    exists (v :: vs1), vs2. rewrite H1. eauto.
Qed.

Lemma app_same_length {A} (l1 l2 l3 l4 : list A) :
  length l1 = length l3 -> l1 ++ l2 = l3 ++ l4 -> l1 = l3 /\ l2 = l4.
Proof.
  revert l3. induction l1 as [| a l1 IH]; intros [| b l3] Hlen Heq; simpl in *; try congruence.
  - split; auto.
  - inv Heq. destruct (IH l3) as [-> ->]; auto.
Qed.

Lemma NoDup_app_intro {A} (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall x, List.In x l1 -> ~ List.In x l2) -> NoDup (l1 ++ l2).
Proof.
  induction l1 as [| a l1 IH]; simpl; intros H1 H2 H3; [ exact H2 |].
  inv H1. constructor.
  - intros Hc. apply in_app_or in Hc as [Hc | Hc]; [ contradiction | eapply H3; [ now left | exact Hc ] ].
  - eapply IH; eauto.
Qed.

Lemma NoDup_remove_mid {A} (l1 l2 l3 : list A) : NoDup (l1 ++ l2 ++ l3) -> NoDup (l1 ++ l3).
Proof.
  intros H. destruct (NoDup_app_split _ _ H) as (H1 & H2 & H3).
  destruct (NoDup_app_split _ _ H2) as (H4 & H5 & H6).
  eapply NoDup_app_intro; eauto. intros x Hx Hc. eapply H3; [ exact Hx |]. apply in_or_app. now right.
Qed.

Lemma get_list_length' {A} (xs : list var) (rho : M.t A) vs : get_list xs rho = Some vs -> length xs = length vs.
Proof.
  revert vs. induction xs as [| x xs IH]; intros vs H; simpl in *; [ inv H; reflexivity |].
  destruct (M.get x rho); try congruence. destruct (get_list xs rho) eqn:H'; try congruence. inv H.
  simpl. f_equal. eauto.
Qed.

Lemma flat_length xs ss yss vs1 :
  length xs = length vs1 -> length ss = length xs -> Forall2 fresh_ok ss yss -> Forall2 shaped ss vs1 ->
  length (flat_vars xs ss yss) = length (flat_vals vs1 ss).
Proof.
  intros Hl1 Hl2 Hfr Hsh. revert xs Hl1 Hl2 yss Hfr.
  induction Hsh as [| s v ss vs Hs Hsh IH]; intros xs Hl1 Hl2 yss Hfr.
  - destruct xs; simpl in *; try congruence; inv Hfr; reflexivity.
  - destruct xs as [| x xs]; simpl in *; try congruence. inv Hfr.
    destruct s as [[[wc n] c] |]; simpl in *.
    + destruct Hs as (us & -> & Hus). rewrite !length_app. erewrite IH; eauto. congruence.
    + subst. simpl. erewrite IH; eauto.
Qed.

Lemma NoDup_flat_vars xs ss yss :
  length xs = length ss -> Forall2 fresh_ok ss yss -> NoDup (xs ++ concat yss) -> NoDup (flat_vars xs ss yss).
Proof.
  revert ss yss. induction xs as [| x xs IH]; intros ss yss Hlen Hfr Hnd.
  - destruct ss; simpl in Hlen; try congruence. inv Hfr. constructor.
  - destruct ss as [| s ss]; simpl in Hlen; try congruence. inv Hlen. inv Hfr.
    rename y into ys, l' into yss. simpl in Hnd. inversion Hnd as [| x' xs' Hxn Hnd' Heq]; subst.
    destruct s as [[[wc n] c] |]; simpl.
    + destruct (NoDup_app_split _ _ Hnd') as (Hn1 & Hn2 & Hn3).
      destruct (NoDup_app_split _ _ Hn2) as (Hn4 & Hn5 & Hn6).
      eapply NoDup_app_intro; [ exact Hn4 | eapply IH; eauto using NoDup_remove_mid |].
      intros z Hz Hc. apply flat_vars_In in Hc as [Hc | Hc]; [ eapply Hn3; [ exact Hc | apply in_or_app; now left ] | eapply Hn6; eauto ].
    + simpl in *. subst ys. simpl in *. constructor; [| eapply IH; eauto ].
      intros Hc. apply flat_vars_In in Hc as [Hc | Hc]; apply Hxn; apply in_or_app; [ now left | now right ].
Qed.

Lemma occurs_free_rebuild_r xs ss yss e z :
  occurs_free e z -> ~ List.In z xs -> occurs_free (rebuild xs ss yss e) z.
Proof.
  revert ss yss. induction xs as [| x xs IH]; intros ss yss Hz Hn; [ destruct ss, yss; exact Hz |].
  destruct ss as [| [[[wc n] c] |] ss], yss as [| ys yss]; simpl; try exact Hz.
  - apply occurs_free_Econstr. right.
    constructor; [ eapply IH; [ exact Hz | intros Hc; apply Hn; now right ] |].
    intros Hc; unfold Ensembles.In in Hc; inv Hc; apply Hn; now left.
  - eapply IH; [ exact Hz | intros Hc; apply Hn; now right ].
Qed.

Lemma get_list_In_nth {A} (xs : list var) (rho : M.t A) vs z :
  get_list xs rho = Some vs -> List.In z xs -> exists v, M.get z rho = Some v /\ List.In v vs.
Proof.
  revert vs. induction xs as [| x xs IH]; intros vs H Hz; [ inv Hz |]. simpl in H.
  destruct (M.get x rho) as [v |] eqn:Hx; try congruence.
  destruct (get_list xs rho) as [vs' |] eqn:H'; try congruence. inv H.
  destruct Hz as [-> | Hz]; [ exists v; split; [ exact Hx | now left ] |].
  edestruct IH as (v' & Hv' & Hin); eauto. exists v'. split; [ exact Hv' | now right ].
Qed.

Lemma occurs_free_proj_fields_r y wc c i zs k z :
  occurs_free k z -> ~ List.In z zs -> occurs_free (proj_fields y wc c i zs k) z.
Proof.
  revert i. induction zs as [| z0 zs IH]; intros i Hz Hn; simpl; [ exact Hz |].
  apply occurs_free_Eproj. right. constructor; [ eapply IH; [ exact Hz | intros Hc; apply Hn; now right ] |].
  intros Hc; unfold Ensembles.In in Hc; inv Hc; apply Hn; now left.
Qed.

Lemma occurs_free_proj_args_r ys ss zss k z :
  occurs_free k z -> ~ List.In z (concat zss) -> occurs_free (proj_args ys ss zss k) z.
Proof.
  revert ss zss. induction ys as [| y ys IH]; intros ss zss Hz Hn; [ destruct ss, zss; exact Hz |].
  destruct ss as [| [[[wc n] c] |] ss], zss as [| zs zss]; simpl in *; try exact Hz.
  - eapply occurs_free_proj_fields_r.
    + eapply IH; [ exact Hz | intros Hc; apply Hn; apply in_or_app; now right ].
    + intros Hc; apply Hn; apply in_or_app; now left.
  - eapply IH; [ exact Hz | intros Hc; apply Hn; apply in_or_app; now right ].
Qed.

Lemma occurs_free_proj_args_args ys ss zss k y :
  List.In y ys -> (forall z, List.In z (concat zss) -> ~ List.In z ys) ->
  length ys = length ss -> Forall pos_ok ss -> Forall2 fresh_ok ss zss ->
  (forall z, List.In z (flat_vars ys ss zss) -> occurs_free k z) ->
  occurs_free (proj_args ys ss zss k) y.
Proof.
  revert ss zss. induction ys as [| y0 ys IH]; intros ss zss Hy Hdis Hlen Hpos Hfr Hk; [ inv Hy |].
  destruct ss as [| s ss]; simpl in Hlen; try congruence. inv Hlen. inv Hpos. inv Hfr.
  rename y1 into zs, l' into zss.
  assert (Hdis' : forall z, List.In z (concat zss) -> ~ List.In z ys).
  { intros z Hz Hc. eapply (Hdis z); [ simpl; apply in_or_app; now right | now right ]. }
  destruct s as [[[wc n] c] |]; simpl in *.
  - assert (Hrest : forall z, List.In z (flat_vars ys ss zss) -> occurs_free k z).
    { intros z Hz. eapply Hk. apply in_or_app. now right. }
    destruct Hy as [-> | Hy].
    + destruct zs as [| z0 zs]; simpl in *; [ lia |].
      apply occurs_free_Eproj. left. constructor.
    + eapply occurs_free_proj_fields_r; [ eapply IH; eauto |].
      intros Hc. eapply (Hdis y); [ apply in_or_app; now left | now right ].
  - subst zs. simpl in *.
    destruct Hy as [-> | Hy].
    + eapply occurs_free_proj_args_r; [ eapply Hk; now left |].
      intros Hc. eapply (Hdis _ Hc). now left.
    + eapply IH; [ exact Hy | exact Hdis' | eassumption | eassumption | eassumption | intros z Hz; eapply Hk; now right ].
Qed.

(** * The arity raising logical relation *)

Section AR_rel.

  Variable (cenv : term.ctor_env).

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  Local Notation PostT := (@exposed.PostT fuel trace).
  Local Notation PostGT := (@exposed.PostGT fuel trace).
  Local Notation VTransT := (@exposed.VTransT fuel trace).

  Variable (La : WM.t (list (option shape))).

  (** Internal closures: calling the source closure on arguments of the
      right shapes is related to calling the target closure on their
      flattened fields. *)
  Definition VT_ar : VTransT :=
    fun PG V' k v1 v2 =>
      match v1, v2 with
      | Vfun rho1 B1 f1, Vfun rho2 B2 f2 =>
          forall vs1 vs2 j w xs1 e1 rho1',
            find_def f1 B1 = Some (w, xs1, e1) ->
            Some rho1' = set_lists xs1 vs1 (def_funs B1 B1 rho1 rho1) ->
            exists ss yss e2,
              WM.get w La = Some ss /\
              find_def f2 B2 = Some (w, flat_vars xs1 ss yss, e2) /\
              (Forall2 shaped ss vs1 ->
               length vs2 = length (flat_vals vs1 ss) ->
               exists rho2',
                 Some rho2' = set_lists (flat_vars xs1 ss yss) vs2 (def_funs B2 B2 rho2 rho2) /\
                 (j < k ->
                  Forall wf_val vs1 ->
                  Forall2 (V' j) (flat_vals vs1 ss) vs2 ->
                  E' cenv V' PG (exposedb w) j (e1, rho1') (e2, rho2')))
      | _, _ => False
      end.

  Global Instance VTransProps_ar : VTransProps VT_ar.
  Proof.
    constructor; unfold VT_ar.
    - intros PG V1 V2 k v1 v2 Hext. destruct v1, v2; try easy.
      intros HVT vs1 vs2 j w xs1 e1 rho1' Hf1 Hs1.
      edestruct HVT as (ss & yss & e2 & HL & Hf2 & Hbody); eauto.
      do 3 eexists. split; [ eassumption | split; [ eassumption |] ].
      intros Hsh Hlen. edestruct Hbody as (rho2' & Hs2 & Hb); eauto.
      eexists; split; eauto. intros Hlt Hwf Hall.
      eapply E'_ext; [| eapply Hb; eauto ].
      + intros. eapply Hext. lia.
      + eapply Forall2_monotonic; [| eassumption ]. intros. eapply Hext; eauto.
    - intros PG V k j v1 v2 Hmono. destruct v1, v2; try easy.
      intros HVT Hleq vs1 vs2 i w xs1 e1 rho1' Hf1 Hs1.
      edestruct HVT as (ss & yss & e2 & HL & Hf2 & Hbody); eauto.
      do 3 eexists. split; [ eassumption | split; [ eassumption |] ].
      intros Hsh Hlen. edestruct Hbody as (rho2' & Hs2 & Hb); eauto.
      eexists; split; eauto. intros Hlt. eapply Hb. lia.
  Qed.

  (** Closures of webs without an entry keep their calling convention. *)
  Definition VT_arS : VTransT := VT_sel cenv (sel_L La) VT_ar.

  Context (PG : PostGT).

  Notation V := (V cenv VT_arS PG).
  Notation E := (E cenv VT_arS PG).
  Notation G := (G cenv VT_arS PG).
  Notation var_rel := (var_rel cenv VT_arS PG).

  Ltac fuel_arith :=
    repeat match goal with
           | [ H : context [ to_nat (_ <+> _) ] |- _ ] => rewrite to_nat_add in H
           | [ |- context [ to_nat (_ <+> _) ] ] => rewrite to_nat_add
           | [ H : context [ to_nat (one_w _) ] |- _ ] => rewrite to_nat_one_w in H
           | [ |- context [ to_nat (one_w _) ] ] => rewrite to_nat_one_w
           end; lia.

  (** ** Target-only steps *)

  Lemma E_add_proj (P : PostT) ex k p1 z w c n y us v e2 rho2
        (Htgt : post_target_step P) :
    M.get y rho2 = Some (Vconstr w c us) ->
    nthN us n = Some v ->
    E P ex k p1 (e2, M.set z v rho2) ->
    E P ex k p1 (Eproj z w c n y e2, rho2).
  Proof.
    destruct p1 as [e1 rho1]. intros Hy Hn HE r1 cin cout Hleq Hs.
    edestruct HE as (r2 & cin' & cout' & Hs2 & HP & HR); eauto.
    do 3 eexists. split; [| split; [ eapply Htgt; [ exact I | eassumption ] | eassumption ] ].
    econstructor 2; [ econstructor; eauto |].
    intros Hex; subst. eapply bstep_fuel_exposed; eauto.
  Qed.

  Lemma E_add_constr_vars (P : PostT) ex k p1 x w t ys vs e2 rho2
        (Htgt : post_target_step P) :
    exposedb w = false ->
    get_list ys rho2 = Some vs ->
    E P ex k p1 (e2, M.set x (Vconstr w t vs) rho2) ->
    E P ex k p1 (Econstr x w t ys e2, rho2).
  Proof.
    destruct p1 as [e1 rho1]. intros Hw Hget HE r1 cin cout Hleq Hs.
    edestruct HE as (r2 & cin' & cout' & Hs2 & HP & HR); eauto.
    do 3 eexists. split; [| split; [ eapply Htgt; [ exact I | eassumption ] | eassumption ] ].
    econstructor 2; [ econstructor; eauto; intros Hc; congruence |].
    intros Hex; subst. eapply bstep_fuel_exposed; eauto.
  Qed.

  (** ** The projections of the call sites *)

  Lemma E_proj_fields (P : PostT) ex k p1 y wc c zs i us e2 rho2
        (Htgt : post_target_step P) :
    wf_env rho2 ->
    M.get y rho2 = Some (Vconstr wc c us) ->
    ~ List.In y zs -> NoDup zs -> i + length zs = length us ->
    (forall rho2', (forall x, ~ List.In x zs -> M.get x rho2' = M.get x rho2) ->
                   get_list zs rho2' = Some (skipn i us) -> wf_env rho2' ->
                   E P ex k p1 (e2, rho2')) ->
    E P ex k p1 (proj_fields y wc c i zs e2, rho2).
  Proof.
    revert i rho2. induction zs as [| z zs IH]; intros i rho2 Hwf Hy Hnin Hnd Hlen He; simpl in *.
    - eapply He; [ reflexivity | | exact Hwf ]. rewrite skipn_all2 by lia. reflexivity.
    - inv Hnd.
      destruct (nth_error us i) as [v |] eqn:Hv; [| apply nth_error_None in Hv; lia ].
      eapply E_add_proj; [ exact Htgt | exact Hy | rewrite nthN_of_nat; exact Hv |].
      eapply IH; [ | | | eassumption | lia |].
      + eapply wf_env_set; [ exact Hwf |].
        pose proof (wf_env_get _ _ _ Hwf Hy) as Hc. inv Hc.
        eapply Forall_forall; [ eassumption | eapply nth_error_In; eassumption ].
      + rewrite M.gso; [ exact Hy |]. intros Hc; subst; apply Hnin; now left.
      + intros Hc; apply Hnin; now right.
      + intros rho2' Hext Hget Hwf'. eapply He; [ | | exact Hwf' ].
        * intros x Hx. rewrite Hext; [| intros Hc; apply Hx; now right ].
          rewrite M.gso; [ reflexivity |]. intros Hc; subst; apply Hx; now left.
        * simpl. rewrite Hget. rewrite Hext by assumption. rewrite M.gss.
          rewrite (skipn_nth_error _ _ _ Hv). reflexivity.
  Qed.

  Lemma get_list_ext (xs : list var) (rho rho' : env) :
    (forall x, List.In x xs -> M.get x rho' = M.get x rho) -> get_list xs rho' = get_list xs rho.
  Proof.
    induction xs as [| x xs IH]; intros H; simpl; [ reflexivity |].
    rewrite H by now left. rewrite IH; [ reflexivity |]. intros; eapply H; now right.
  Qed.

  Lemma E_proj_args (P : PostT) ex k p1 ys ss zss vs2 e2 rho2
        (Htgt : post_target_step P) :
    length ys = length ss -> Forall2 fresh_ok ss zss ->
    NoDup (concat zss) -> Disjoint _ (FromList (concat zss)) (FromList ys) ->
    get_list ys rho2 = Some vs2 -> Forall2 shaped ss vs2 -> wf_env rho2 ->
    (forall rho2', (forall x, ~ List.In x (concat zss) -> M.get x rho2' = M.get x rho2) ->
                   get_list (flat_vars ys ss zss) rho2' = Some (flat_vals vs2 ss) -> wf_env rho2' ->
                   E P ex k p1 (e2, rho2')) ->
    E P ex k p1 (proj_args ys ss zss e2, rho2).
  Proof.
    revert ss zss vs2 rho2. induction ys as [| y ys IH]; intros ss zss vs2 rho2 Hlen Hfr Hnd Hdis Hget Hsh Hwf He.
    - destruct ss; simpl in Hlen; try congruence. inv Hfr. inv Hget. simpl. eapply He; [ reflexivity | reflexivity | exact Hwf ].
    - destruct ss as [| s ss]; simpl in Hlen; try congruence. inv Hlen. inv Hfr.
      rename y0 into zs, l' into zss.
      simpl in Hget. destruct (M.get y rho2) as [v |] eqn:Hy; try congruence.
      destruct (get_list ys rho2) as [vs |] eqn:Hys; try congruence. inv Hget. inv Hsh.
      simpl in Hnd. destruct (NoDup_app_split _ _ Hnd) as (Hnd1 & Hnd2 & Hnd3).
      assert (Hdis' : Disjoint _ (FromList (concat zss)) (FromList ys)).
      { constructor. intros z Hz. inv Hz. eapply Hdis. constructor.
        - unfold FromList, Ensembles.In in *. simpl. apply in_or_app. now right.
        - now right. }
      destruct s as [[[wc n] c] |]; simpl in *.
      + match goal with H : exists us, v = Vconstr _ _ us /\ _ |- _ => destruct H as (us & -> & Hus) end.
        eapply (E_proj_fields P ex k p1 y wc c zs 0 us); [ exact Htgt | exact Hwf | exact Hy | | exact Hnd1 | rewrite Hus; simpl; eassumption |].
        { intros Hc. eapply Hdis. constructor; [| now left ].
          unfold FromList, Ensembles.In. simpl. apply in_or_app. now left. }
        intros rho2' Hext' Hzs Hwf'.
        eapply IH; [ eassumption | eassumption | exact Hnd2 | exact Hdis' | | eassumption | exact Hwf' |].
        { rewrite (get_list_ext ys rho2 rho2'); [ exact Hys |]. intros x Hx. eapply Hext'.
          intros Hc. eapply Hdis. constructor; [| right; exact Hx ].
          unfold FromList, Ensembles.In. simpl. apply in_or_app. now left. }
        intros rho2'' Hext'' Hflat Hwf''. eapply He; [ | | exact Hwf'' ].
        * intros x Hx. rewrite Hext''; [| intros Hc; apply Hx; apply in_or_app; now right ].
          eapply Hext'. intros Hc; apply Hx; apply in_or_app; now left.
        * eapply get_list_app; [| exact Hflat ].
          rewrite (get_list_ext zs rho2' rho2''); [ exact Hzs |]. intros x Hx. eapply Hext''. eapply Hnd3. exact Hx.
      + subst zs. simpl in *.
        eapply IH; [ eassumption | eassumption | exact Hnd | exact Hdis' | exact Hys | eassumption | exact Hwf |].
        intros rho2'' Hext'' Hflat Hwf''. eapply He; [ exact Hext'' | | exact Hwf'' ].
        simpl. rewrite Hflat. rewrite Hext''; [ rewrite Hy; reflexivity |].
        intros Hc. eapply Hdis. constructor; [ exact Hc | now left ].
  Qed.

  (** ** The rebuilds of the function entries *)

  Lemma E_rebuild (P : PostT) ex k p1 j xs ss yss vs1 vs2 e2 rho2
        (Htgt : post_target_step P) :
    length xs = length ss -> Forall2 fresh_ok ss yss -> Forall info_ok ss ->
    NoDup (xs ++ concat yss) ->
    get_list (flat_vars xs ss yss) rho2 = Some vs2 ->
    Forall2 shaped ss vs1 ->
    Forall2 (V j) (flat_vals vs1 ss) vs2 ->
    (forall rho2', (forall x, ~ List.In x xs -> M.get x rho2' = M.get x rho2) ->
                   (exists vs2', get_list xs rho2' = Some vs2' /\ Forall2 (V j) vs1 vs2') ->
                   E P ex k p1 (e2, rho2')) ->
    E P ex k p1 (rebuild xs ss yss e2, rho2).
  Proof.
    revert ss yss vs1 vs2 rho2. induction xs as [| x xs IH];
      intros ss yss vs1 vs2 rho2 Hlen Hfr Hinfo Hnd Hget Hsh Hvs He.
    - destruct ss; simpl in Hlen; try congruence. inv Hfr. inv Hsh. simpl in *.
      eapply He; [ reflexivity | exists []; split; [ reflexivity | constructor ] ].
    - destruct ss as [| s ss]; simpl in Hlen; try congruence. inv Hlen. inv Hfr. inv Hinfo. inv Hsh.
      rename y into ys, l' into yss, y0 into v1, l'0 into vs1.
      assert (Hx : ~ List.In x xs) by (inv Hnd; intros Hc; eauto using in_or_app).
      assert (Hxy : ~ List.In x (concat (ys :: yss))) by (inv Hnd; intros Hc; eauto using in_or_app).
      assert (Hnd' : NoDup (xs ++ concat (ys :: yss))) by (inv Hnd; assumption).
      destruct s as [[[wc n] c] |]; simpl in *.
      + match goal with H : exists us, v1 = Vconstr _ _ us /\ _ |- _ => destruct H as (us1 & -> & Hus1) end.
        apply get_list_app_inv in Hget as (us2 & vs2' & -> & Hys & Hrest).
        apply Forall2_app_inv_l in Hvs as (l1 & l2 & Hv1 & Hv2 & Heq).
        assert (Hl : l1 = us2 /\ l2 = vs2').
        { eapply app_same_length; [| exact (eq_sym Heq) ].
          rewrite <- (Forall2_length _ _ _ Hv1). rewrite Hus1.
          rewrite <- (get_list_length' _ _ _ Hys). symmetry. eassumption. }
        destruct Hl as [-> ->].
        eapply E_add_constr_vars; [ exact Htgt | eassumption | exact Hys |].
        eapply IH; [ eassumption | eassumption | eassumption | | | eassumption | exact Hv2 |].
        * eapply NoDup_remove_mid. exact Hnd'.
        * rewrite get_list_set_neq; [ exact Hrest |].
          intros Hc. apply flat_vars_In in Hc as [Hc | Hc]; [ contradiction |].
          apply Hxy. apply in_or_app. now right.
        * intros rho2' Hext (vs2'' & Hget' & Hvs'). eapply He.
          -- intros z Hz. rewrite Hext; [| intros Hc; apply Hz; now right ].
             rewrite M.gso; [ reflexivity |]. intros Hc; subst; apply Hz; now left.
          -- exists (Vconstr wc c us2 :: vs2''). split.
             ++ simpl. rewrite Hget'. rewrite Hext by assumption. rewrite M.gss. reflexivity.
             ++ constructor; [| exact Hvs' ].
                eapply (V_Vconstr cenv VT_arS); [ intros Hc; congruence | exact Hv1 ].
      + subst ys. simpl in *.
        destruct (M.get x rho2) as [v2 |] eqn:Hx2; try congruence.
        destruct (get_list (flat_vars xs ss yss) rho2) as [vs2' |] eqn:Hrest; try congruence. inv Hget.
        inv Hvs.
        eapply IH; [ eassumption | eassumption | eassumption | exact Hnd' | exact Hrest | eassumption | eassumption |].
        intros rho2' Hext (vs2'' & Hget' & Hvs'). eapply He.
        * intros z Hz. eapply Hext. intros Hc; apply Hz; now right.
        * exists (v2 :: vs2''). split; [| constructor; eauto ].
          simpl. rewrite Hget'. rewrite Hext by assumption. rewrite Hx2. reflexivity.
  Qed.

  (** ** Calls of transformed webs *)

  Lemma shaped_V j ss vs1 vs2 :
    Forall2 shaped ss vs1 -> Forall2 (V j) vs1 vs2 ->
    Forall2 shaped ss vs2 /\ Forall2 (V j) (flat_vals vs1 ss) (flat_vals vs2 ss).
  Proof.
    intros Hsh. revert vs2. induction Hsh as [| s v1 ss vs1 Hs Hsh IH]; intros vs2 Hvs.
    - inv Hvs. split; constructor.
    - inv Hvs. rename y into v2, l' into vs2. destruct (IH _ H3) as [Hsh2 Hflat].
      destruct s as [[[wc n] c] |]; simpl in *.
      + destruct Hs as (us1 & -> & Hus1).
        destruct (V_Vconstr_l cenv VT_arS PG _ _ _ _ _ H1) as (us2 & -> & Hus).
        split; [ constructor; [ exists us2; split; [ reflexivity | rewrite <- (Forall2_length _ _ _ Hus); exact Hus1 ] | exact Hsh2 ] |].
        eapply Forall2_app; eassumption.
      + split; [ constructor; [ exact I | exact Hsh2 ] | constructor; eauto ].
  Qed.

  Context {P : PostT} {Hprops : Post_properties cenv P P PG} (Htgt : post_target_step P).

  Lemma E_call_inner ex k rho1 rho2 f w ys ys2 ss vs1 vs2 :
    exposedb w = false ->
    WM.get w La = Some ss ->
    get_list ys rho1 = Some vs1 ->
    get_list ys2 rho2 = Some (flat_vals vs2 ss) ->
    Forall2 shaped ss vs1 ->
    Forall2 (V k) (flat_vals vs1 ss) (flat_vals vs2 ss) ->
    wf_env rho1 ->
    var_rel k rho1 rho2 f f ->
    E P ex k (Eapp f w ys, rho1) (Eapp f w ys2, rho2).
  Proof.
    pose proof Hprops as Hp. destruct Hp.
    intros Hw HL Hg1 Hg2 Hsh Hvs Hwf Hfun r1 cin cout Hleq Hstep. inv Hstep.
    - exists OOT, cin, <0>. split; [ constructor; eapply lt_one_w; eassumption |].
      split; [ match goal with H : post_OOT P |- _ => eapply H end; eapply lt_one_w; eassumption | exact I ].
    - inv H. rewrite Hg1 in H5. injection H5 as Hvv. subst vs.
      edestruct Hfun as (v2 & Hget2 & Hv); eauto.
      eapply (V_sel_internal cenv (sel_L La) VT_ar PG) in Hv;
        [| eassumption | eassumption | eapply sel_L_Some; eassumption ].
      destruct v2; try contradiction.
      edestruct (Hv vs1 (flat_vals vs2 ss) (k - 1)) as (ss' & yss & e2 & HL' & Hf2 & Hbody); eauto.
      rewrite HL in HL'. inv HL'.
      edestruct Hbody as (rho2' & Hset2 & Hb); [ exact Hsh | symmetry; eapply Forall2_length; eauto |].
      edestruct Hb as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
        [ fuel_arith | eapply wf_env_get_list; eauto | | | eassumption | ].
      + eapply (V_mono_Forall2 cenv VT_arS); eauto. lia.
      + fuel_arith.
      + do 3 eexists. split; [| split ].
        * econstructor 2; [ econstructor; eauto |].
          -- intros Hc; congruence.
          -- eapply (R_exposed_ex cenv VT_arS); eauto.
        * match goal with H : post_app_compat P PG |- _ => eapply H end; eauto.
        * eapply (R_mono cenv VT_arS); eauto. fuel_arith.
  Qed.

  Lemma E_letapp_inner ex k rho1 rho2 x f w ys ys2 ss vs1 vs2 e1 e2 :
    exposedb w = false ->
    WM.get w La = Some ss ->
    get_list ys rho1 = Some vs1 ->
    get_list ys2 rho2 = Some (flat_vals vs2 ss) ->
    Forall2 shaped ss vs1 ->
    Forall2 (V k) (flat_vals vs1 ss) (flat_vals vs2 ss) ->
    wf_env rho1 ->
    var_rel k rho1 rho2 f f ->
    (forall m v1 v2, m < k -> V m v1 v2 -> E P ex m (e1, M.set x v1 rho1) (e2, M.set x v2 rho2)) ->
    E P ex k (Eletapp x f w ys e1, rho1) (Eletapp x f w ys2 e2, rho2).
  Proof.
    pose proof Hprops as Hp. destruct Hp.
    intros Hw HL Hg1 Hg2 Hsh Hvs Hwf Hfun Hk r1 cin cout Hleq Hstep. inv Hstep.
    - exists OOT, cin, <0>. split; [ constructor; eapply lt_one_w; eassumption |].
      split; [ match goal with H : post_OOT P |- _ => eapply H end; eapply lt_one_w; eassumption | exact I ].
    - inv H;
        (match goal with H' : get_list ys rho1 = Some ?vs |- _ =>
           rewrite Hg1 in H'; injection H' as Hvv; rewrite <- Hvv in *; clear Hvv end;
         edestruct Hfun as (v2 & Hget2 & Hv); eauto;
         eapply (V_sel_internal cenv (sel_L La) VT_ar PG) in Hv;
         [| eassumption | eassumption | eapply sel_L_Some; eassumption ];
         destruct v2; try contradiction;
         edestruct (Hv vs1 (flat_vals vs2 ss) (k - 1)) as (ss' & yss & eb2 & HL' & Hf2 & Hbody); eauto;
         rewrite HL in HL'; inv HL';
         edestruct Hbody as (rho2' & Hset2 & Hb); [ exact Hsh | symmetry; eapply Forall2_length; eauto |]).
      + edestruct Hb as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
          [ fuel_arith | eapply wf_env_get_list; eauto | | | eassumption | ].
        * eapply (V_mono_Forall2 cenv VT_arS); eauto. lia.
        * fuel_arith.
        * destruct r2 as [| v2]; try contradiction. simpl in HR.
          edestruct (Hk (k - 1 - to_nat cin1)) as (r2 & cin'' & cout'' & Hstep3 & Hpost' & HR');
            [ fuel_arith | eassumption | | eassumption | ]; [ fuel_arith | ].
          do 3 eexists. split; [| split ].
          -- econstructor 2; [ econstructor; eauto |].
             ++ intros Hc; congruence.
             ++ eapply (R_exposed_ex cenv VT_arS); eauto.
          -- match goal with H : post_letapp_compat _ P P PG |- _ => eapply H end; eauto.
          -- eapply (R_mono cenv VT_arS); eauto. fuel_arith.
      + edestruct Hb as (r2 & cin' & cout' & Hstep2 & Hpost & HR);
          [ fuel_arith | eapply wf_env_get_list; eauto | | | eassumption | ].
        * eapply (V_mono_Forall2 cenv VT_arS); eauto. lia.
        * fuel_arith.
        * destruct r2; try contradiction.
          do 3 eexists. split; [| split ].
          -- econstructor 2; [ eapply BStept_letapp_oot; eauto; intros Hc; congruence |].
             intros; exact I.
          -- match goal with H : post_letapp_compat_OOT P PG |- _ => eapply H end; eauto.
          -- exact I.
  Qed.

  (** A source term whose variables are unbound only steps to [OOT] *)
  Lemma E_stuck_args ex k e1 rho1 e2 rho2 ys :
    get_list ys rho1 = None ->
    (forall cin r cout, bstep cenv ex rho1 e1 cin r cout -> exists vs, get_list ys rho1 = Some vs) ->
    E P ex k (e1, rho1) (e2, rho2).
  Proof.
    pose proof Hprops as Hp. destruct Hp.
    intros Hnone Hstuck r1 cin cout Hleq Hstep. inv Hstep.
    - exists OOT, cin, <0>. split; [ constructor; eapply lt_one_w; eassumption |].
      split; [ match goal with H : post_OOT P |- _ => eapply H end; eapply lt_one_w; eassumption | exact I ].
    - edestruct Hstuck as (vs & Hvs); eauto. congruence.
  Qed.

  Lemma E_app_ar ex k K rho1 rho2 f w ys ss zss :
    exposedb w = false -> WM.get w La = Some ss -> length ys = length ss ->
    K_inv K rho1 -> shape_ok K ys ss ->
    Forall2 fresh_ok ss zss -> NoDup (concat zss) -> Disjoint _ (FromList (concat zss)) (f |: FromList ys) ->
    wf_env rho1 -> wf_env rho2 -> var_rel k rho1 rho2 f f -> Forall2 (var_rel k rho1 rho2) ys ys ->
    E P ex k (Eapp f w ys, rho1) (proj_args ys ss zss (Eapp f w (flat_vars ys ss zss)), rho2).
  Proof.
    intros Hw HL Hlen HK Hok Hfr Hnd Hdis Hwf Hwf2 Hfun Hall.
    destruct (get_list ys rho1) as [vs1 |] eqn:Hg1.
    - edestruct (var_rel_get_list cenv VT_arS PG) as (vs2 & Hg2 & Hvs); [ exact Hall | exact Hg1 |].
      pose proof (shape_ok_vals _ _ _ _ _ HK Hok Hg1 Hlen) as Hsh1.
      destruct (shaped_V _ _ _ _ Hsh1 Hvs) as [Hsh2 Hflat].
      eapply E_proj_args; [ exact Htgt | exact Hlen | exact Hfr | exact Hnd | | exact Hg2 | exact Hsh2 | exact Hwf2 |].
      { eapply Disjoint_Included_r; [| exact Hdis ]. sets. }
      intros rho2' Hext Hgf _. eapply E_call_inner; eauto.
      intros v1 Hget1. edestruct Hfun as (v2 & Hget2 & Hv); eauto. exists v2. split; [| exact Hv ].
      rewrite Hext; [ exact Hget2 |]. intros Hc. eapply Hdis. constructor; [ exact Hc | now left ].
    - eapply E_stuck_args; [ exact Hg1 |]. intros cin r cout Hs. inv Hs. eauto.
  Qed.

  Lemma E_letapp_ar ex k K rho1 rho2 x f w ys ss zss e1 e2 :
    exposedb w = false -> WM.get w La = Some ss -> length ys = length ss ->
    K_inv K rho1 -> shape_ok K ys ss ->
    Forall2 fresh_ok ss zss -> NoDup (concat zss) -> Disjoint _ (FromList (concat zss)) (f |: FromList ys) ->
    wf_env rho1 -> wf_env rho2 -> var_rel k rho1 rho2 f f -> Forall2 (var_rel k rho1 rho2) ys ys ->
    (forall rho2', (forall z, ~ List.In z (concat zss) -> M.get z rho2' = M.get z rho2) -> wf_env rho2' ->
                   forall m v1 v2, m < k -> V m v1 v2 ->
                                   E P ex m (e1, M.set x v1 rho1) (e2, M.set x v2 rho2')) ->
    E P ex k (Eletapp x f w ys e1, rho1)
      (proj_args ys ss zss (Eletapp x f w (flat_vars ys ss zss) e2), rho2).
  Proof.
    intros Hw HL Hlen HK Hok Hfr Hnd Hdis Hwf Hwf2 Hfun Hall Hk.
    destruct (get_list ys rho1) as [vs1 |] eqn:Hg1.
    - edestruct (var_rel_get_list cenv VT_arS PG) as (vs2 & Hg2 & Hvs); [ exact Hall | exact Hg1 |].
      pose proof (shape_ok_vals _ _ _ _ _ HK Hok Hg1 Hlen) as Hsh1.
      destruct (shaped_V _ _ _ _ Hsh1 Hvs) as [Hsh2 Hflat].
      eapply E_proj_args; [ exact Htgt | exact Hlen | exact Hfr | exact Hnd | | exact Hg2 | exact Hsh2 | exact Hwf2 |].
      { eapply Disjoint_Included_r; [| exact Hdis ]. sets. }
      intros rho2' Hext Hgf Hwf2'. eapply E_letapp_inner; eauto.
      intros v1 Hget1. edestruct Hfun as (v2 & Hget2 & Hv); eauto. exists v2. split; [| exact Hv ].
      rewrite Hext; [ exact Hget2 |]. intros Hc. eapply Hdis. constructor; [ exact Hc | now left ].
    - eapply E_stuck_args; [ exact Hg1 |]. intros cin r cout Hs. inv Hs; eauto.
  Qed.

  (** ** Environments of function bodies *)

  Lemma G_params_vars j xs vs1 vs2 rho1 rho1' rho2 :
    NoDup xs -> set_lists xs vs1 rho1 = Some rho1' -> get_list xs rho2 = Some vs2 ->
    Forall2 (V j) vs1 vs2 -> forall z, List.In z xs -> var_rel j rho1' rho2 z z.
  Proof.
    revert vs1 vs2 rho1'. induction xs as [| x xs IH]; intros vs1 vs2 rho1' Hnd Hs Hg Hvs z Hz; [ inv Hz |].
    destruct vs1 as [| v1 vs1]; simpl in Hs; try congruence.
    destruct (set_lists xs vs1 rho1) as [rho1'' |] eqn:Hs'; inv Hs.
    simpl in Hg. destruct (M.get x rho2) as [v2 |] eqn:Hx; try congruence.
    destruct (get_list xs rho2) as [vs2' |] eqn:Hg'; try congruence. inv Hg. inv Hvs. inv Hnd.
    destruct (peq z x) as [-> | Hne].
    - intros v Hv. rewrite M.gss in Hv. inv Hv. eexists; split; eauto.
    - destruct Hz as [Hz | Hz]; [ congruence |].
      intros v Hv. rewrite M.gso in Hv by assumption. eapply IH; eauto.
  Qed.

  Lemma wf_env_params xs vs2 rho2 rho2' :
    wf_env rho2 -> (forall z, ~ List.In z xs -> M.get z rho2' = M.get z rho2) ->
    get_list xs rho2' = Some vs2 -> Forall wf_val vs2 -> wf_env rho2'.
  Proof.
    intros Hwf Hext Hg Hvs. constructor. intros z v Hz.
    destruct (in_dec peq z xs) as [Hin | Hnin].
    - destruct (get_list_In_nth xs rho2' vs2 z Hg Hin) as (v' & Hv' & Hin'). rewrite Hz in Hv'. inv Hv'.
      eapply Forall_forall; eauto.
    - rewrite Hext in Hz by assumption. eapply wf_env_get; eauto.
  Qed.

  Lemma G_params j S xs vs1 vs2 rho1 rho1' rho2 rho2' (D : Ensemble var) :
    G j (S \\ FromList xs) rho1 rho2 ->
    NoDup xs -> set_lists xs vs1 rho1 = Some rho1' ->
    (forall z, ~ List.In z xs -> ~ D z -> M.get z rho2' = M.get z rho2) ->
    Disjoint _ D S ->
    get_list xs rho2' = Some vs2 -> Forall2 (V j) vs1 vs2 -> wf_env rho2' ->
    G j S rho1' rho2'.
  Proof.
    intros (Hwf1 & Hwf2 & HG) Hnd Hs Hext Hdis Hg Hvs Hwf2'.
    split; [| split; [ exact Hwf2' |] ].
    - eapply (wf_env_set_lists rho1 rho1' xs vs1); [ exact Hwf1 | eapply (Forall2_V_wf_l cenv VT_arS); eauto | exact Hs ].
    - intros z Hz. destruct (in_dec peq z xs) as [Hin | Hnin].
      + eapply G_params_vars; eauto.
      + intros v1 Hv1. erewrite <- set_lists_not_In in Hv1; [| eassumption | eassumption ].
        edestruct HG as (v2 & Hv2 & Hv); [ constructor; [ exact Hz | exact Hnin ] | exact Hv1 |].
        exists v2. split; [| exact Hv ]. rewrite Hext; [ exact Hv2 | exact Hnin |].
        intros Hc. eapply Hdis. constructor; eassumption.
  Qed.

  (** ** Closures of transformed bundles *)

  Definition IH_exp k :=
    forall m K ex e e' rho1 rho2,
      m < k ->
      trans La K e e' ->
      K_inv K rho1 ->
      G m (occurs_free e') rho1 rho2 ->
      E P ex m (e, rho1) (e', rho2).

  Lemma Vfun_ar k K rho1 rho2 B B' :
    trans_fundefs La K B B' ->
    IH_exp k ->
    K_inv K (def_funs B B rho1 rho1) ->
    G k (occurs_free_fundefs B') rho1 rho2 ->
    forall f, name_in_fundefs B f -> V k (Vfun rho1 B f) (Vfun rho2 B' f).
  Proof.
    pose proof Hprops as Hp. destruct Hp.
    intros HB. induction k as [k IHk] using lt_wf_rec. intros Hexp HK HG f Hin.
    assert (Hdefs : forall j, j < k -> forall g, name_in_fundefs B g ->
                                      V j (Vfun rho1 B g) (Vfun rho2 B' g)).
    { intros j Hlt g Hg. eapply IHk; eauto.
      - intros m K' ex e e' r1 r2 Hm. eapply Hexp. lia.
      - eapply (G_mono cenv VT_arS); eauto. lia. }
    (* the environments of the bodies, before the parameters *)
    assert (Hbase : forall j S, j < k ->
               S \subset name_in_fundefs B' :|: occurs_free_fundefs B' ->
               G j S (def_funs B B rho1 rho1) (def_funs B' B' rho2 rho2)).
    { intros j S Hlt HS.
      eapply (G_def_funs cenv VT_arS); try (now apply HG).
      - eapply (G_antimon cenv VT_arS). eapply (G_mono cenv VT_arS); eauto. lia.
        intros z [Hz Hn]. eapply HS in Hz. destruct Hz as [z Hz | z Hz]; [| exact Hz ].
        exfalso. apply Hn. eapply trans_fundefs_names; eauto.
      - eapply trans_fundefs_names; eauto.
      - intros g Hg. eapply Hdefs; eauto. }
    edestruct name_in_fundefs_find_def as (w & xs & e & Hfind); eauto.
    edestruct trans_fundefs_find_def as
        (e' & [ (Hw & Htrans & Hfind')
              | (ss & yss & Hw & HL & Hlen & Hinfo & Hfr & Hnd & Hdis & Htrans & Hfind') ]); eauto.
    - (* functions that keep their calling convention *)
      eapply (V_Vfun_keeps cenv (sel_L La) VT_ar PG); eauto; try now apply HG.
      eapply (V_fun_def cenv VT_arS); eauto.
      intros j vs1 vs2 rho1' rho2' Hlt Hexpv Hvs Hs1 Hs2.
      eapply (E_post_mono cenv VT_arS); [ eassumption |].
      eapply Hexp; eauto.
      + eapply K_inv_set_lists; [ eassumption | right; reflexivity | eassumption ].
      + eapply (G_set_lists cenv VT_arS); eauto.
        eapply Hbase; [ eassumption |].
        intros z [Hz Hn]. edestruct (occurs_free_in_fun _ _ _ _ _ Hfind' z Hz) as [z' Hz' | z' Hz'];
          [ contradiction | exact Hz' ].
    - (* transformed functions: rebuild the flattened parameters on entry *)
      eapply (V_Vfun_sel cenv (sel_L La) VT_ar PG);
        [ now apply HG | constructor; apply HG | eapply not_exposed_Vfun; eassumption
        | eassumption | eassumption | eapply sel_L_Some; eassumption |].
      unfold VT_ar; cbn -[E']. intros vs1 vs2 j w' xs1 e1 rho1' Hf1 Hs1.
      rewrite Hfind in Hf1. inv Hf1.
      exists ss, yss, (rebuild xs1 ss yss e'). split; [ eassumption | split; [ eassumption |] ].
      intros Hsh Hlen2.
      assert (Hlxs : length xs1 = length vs1) by (eapply set_lists_length_eq; symmetry; eassumption).
      edestruct (set_lists_length3 (def_funs B' B' rho2 rho2) (flat_vars xs1 ss yss) vs2) as [rho2' Hs2].
      { rewrite Hlen2. eapply flat_length; eauto. }
      eexists; split; [ symmetry; eassumption |].
      intros Hlt Hwf Hvs.
      assert (Hlen' : length xs1 = length ss) by congruence.
      assert (Hndf : NoDup (flat_vars xs1 ss yss)) by (eapply NoDup_flat_vars; eauto).
      assert (Hndx : NoDup xs1) by (destruct (NoDup_app_split _ _ Hnd); tauto).
      eapply (E_post_mono cenv VT_arS); [ eassumption |].
      eapply E_rebuild; [ exact Htgt | exact Hlen' | exact Hfr | exact Hinfo | exact Hnd
                        | eapply get_list_set_lists; eauto | exact Hsh | exact Hvs |].
      intros rho2'' Hext (vs2'' & Hget'' & Hvs'').
      eapply Hexp; [ exact Hlt | exact Htrans | |].
      + eapply K_inv_set_lists; [ exact HK | left; exact Hsh | symmetry; exact Hs1 ].
      + eapply G_params with (rho2 := def_funs B' B' rho2 rho2) (D := FromList (concat yss));
          [ | exact Hndx | symmetry; exact Hs1 | | exact Hdis | exact Hget'' | exact Hvs'' | ].
        * eapply Hbase; [ exact Hlt |].
          intros z [Hz Hn].
          assert (Hz' : occurs_free (rebuild xs1 ss yss e') z) by (eapply occurs_free_rebuild_r; eauto).
          edestruct (occurs_free_in_fun _ _ _ _ _ Hfind' z Hz') as [z' Hz'' | z' Hz''].
          -- exfalso. apply flat_vars_In in Hz'' as [Hc | Hc]; [ contradiction |].
             eapply Hdis. constructor; eassumption.
          -- exact Hz''.
        * intros z Hz1 Hz2. rewrite Hext by assumption.
          erewrite <- set_lists_not_In; [ reflexivity | eassumption |].
          intros Hc. apply flat_vars_In in Hc as [Hc | Hc]; contradiction.
        * eapply wf_env_params; [| exact Hext | exact Hget'' | eapply (Forall2_V_wf_r cenv VT_arS); eauto ].
          eapply wf_env_set_lists; [| | eassumption ].
          -- eapply wf_env_def_funs; apply HG.
          -- eapply (Forall2_V_wf_r cenv VT_arS); eauto.
  Qed.

  (** ** Fundamental property *)

  Lemma G_ext_r k S rho1 rho2 rho2' :
    G k S rho1 rho2 -> (forall z, S z -> M.get z rho2' = M.get z rho2) -> wf_env rho2' -> G k S rho1 rho2'.
  Proof.
    intros (Hwf1 & Hwf2 & HG) Hext Hwf2'. split; [ exact Hwf1 | split; [ exact Hwf2' |] ].
    intros z Hz v1 Hv1. edestruct HG as (v2 & Hv2 & Hv); eauto. exists v2. rewrite Hext; eauto.
  Qed.

  Lemma Forall2_var_rel_In k rho1 rho2 (ys : list var) :
    (forall y, List.In y ys -> var_rel k rho1 rho2 y y) -> Forall2 (var_rel k rho1 rho2) ys ys.
  Proof. induction ys as [| y ys IH]; intros H; constructor; [ eapply H; now left | eapply IH; intros; eapply H; now right ]. Qed.

  Ltac solve_K :=
    first [ eassumption
          | eapply K_inv_remove; eassumption
          | eapply K_inv_def_funs; eassumption ].

  Ltac solve_G_set :=
    eapply (G_set cenv VT_arS); eauto; eapply (G_antimon cenv VT_arS);
    [ eapply (G_mono cenv VT_arS); eauto; lia | normalize_occurs_free; sets ].

  Lemma fundamental k K ex e e' rho1 rho2 :
    trans La K e e' ->
    K_inv K rho1 ->
    G k (occurs_free e') rho1 rho2 ->
    E P ex k (e, rho1) (e', rho2).
  Proof.
    pose proof Hprops as Hp. destruct Hp.
    revert K ex e e' rho1 rho2.
    induction k as [k IH] using lt_wf_rec.
    assert (IH' : IH_exp k) by (intros m K ex e e' r1 r2 Hlt; eapply IH; eauto).
    intros K ex e e' rho1 rho2 Htrans. revert ex rho1 rho2.
    induction Htrans; intros ex rho1 rho2 HK HG.
    - (* Econstr *)
      eapply (E_constr_compat_vals cenv VT_arS); eauto.
      + eapply (G_Forall2_var_rel cenv VT_arS); eauto. normalize_occurs_free. sets.
      + intros m vs1 v2 Hlt Hget Hv.
        eapply IH; [ lia | eassumption | | solve_G_set ].
        eapply K_inv_set; [ eassumption |]. exists vs1. split; [ reflexivity |].
        symmetry. eapply get_list_length'. eassumption.
    - (* Eproj *)
      eapply (E_proj_compat cenv VT_arS); eauto.
      + eapply (G_var_rel cenv VT_arS); eauto. fv_mem.
      + intros m v1 v2 Hlt Hv.
        eapply IH; [ lia | eassumption | solve_K | solve_G_set ].
    - (* Ecase [] *)
      eapply (E_case_nil_compat cenv VT_arS); eauto.
    - (* Ecase (_ :: _) *)
      eapply (E_case_cons_compat cenv VT_arS); eauto.
      + eapply trans_case_tags; eauto.
      + eapply (G_var_rel cenv VT_arS); eauto. fv_mem.
      + intros m Hlt. eapply IH; [ lia | eassumption | solve_K |].
        eapply (G_antimon cenv VT_arS). eapply (G_mono cenv VT_arS); eauto. lia.
        normalize_occurs_free. sets.
      + eapply IHHtrans2; eauto.
        eapply (G_antimon cenv VT_arS); eauto. normalize_occurs_free. sets.
    - (* Eletapp, kept *)
      eapply (E_letapp_compat cenv VT_arS); eauto.
      + eapply (var_rel_keeps_fun cenv (sel_L La) VT_ar PG); eauto. eapply (G_var_rel cenv VT_arS); eauto. fv_mem.
      + eapply (G_Forall2_var_rel cenv VT_arS); eauto. normalize_occurs_free. sets.
      + intros m v1 v2 Hlt _ Hv.
        eapply IH; [ lia | eassumption | solve_K | solve_G_set ].
    - (* Eletapp, transformed *)
      assert (Hdl : forall z, List.In z (concat zss) -> ~ List.In z ys).
      { intros z Hz Hc. eapply H6. constructor; [ exact Hz | now right ]. }
      assert (Hfree : forall z, List.In z (flat_vars ys ss zss) -> occurs_free (Eletapp x f w (flat_vars ys ss zss) e') z).
      { intros z Hz. apply occurs_free_Eletapp. left. now right. }
      eapply E_letapp_ar; eauto.
      + apply HG.
      + apply HG.
      + eapply (G_var_rel cenv VT_arS); eauto.
        eapply occurs_free_proj_args_r.
        * apply occurs_free_Eletapp. left. now left.
        * intros Hc. eapply H6. constructor; [ exact Hc | now left ].
      + eapply Forall2_var_rel_In. intros y Hy. eapply (G_var_rel cenv VT_arS); eauto.
        eapply occurs_free_proj_args_args; eauto.
      + intros rho2' Hext Hwf2' m v1 v2 Hlt Hv.
        eapply IH; [ lia | eassumption | solve_K |].
        eapply (G_set cenv VT_arS); [| exact Hv ].
        eapply G_ext_r; [| | exact Hwf2' ].
        * eapply (G_antimon cenv VT_arS); [ eapply (G_mono cenv VT_arS); [ exact HG | lia ] |].
          intros z [Hz Hn]. eapply occurs_free_proj_args_r.
          -- apply occurs_free_Eletapp. right. constructor; eassumption.
          -- intros Hc. eapply H7. constructor; [ exact Hc | constructor; eassumption ].
        * intros z [Hz Hn]. eapply Hext. intros Hc. eapply H7. constructor; [ exact Hc | constructor; eassumption ].
    - (* Eapp, kept *)
      eapply (E_app_compat cenv VT_arS); eauto.
      + eapply (var_rel_keeps_fun cenv (sel_L La) VT_ar PG); eauto. eapply (G_var_rel cenv VT_arS); eauto. fv_mem.
      + eapply (G_Forall2_var_rel cenv VT_arS); eauto. normalize_occurs_free. sets.
    - (* Eapp, transformed *)
      assert (Hdl : forall z, List.In z (concat zss) -> ~ List.In z ys).
      { intros z Hz Hc. eapply H6. constructor; [ exact Hz | now right ]. }
      eapply E_app_ar; eauto.
      + apply HG.
      + apply HG.
      + eapply (G_var_rel cenv VT_arS); eauto.
        eapply occurs_free_proj_args_r.
        * apply occurs_free_Eapp. now right.
        * intros Hc. eapply H6. constructor; [ exact Hc | now left ].
      + eapply Forall2_var_rel_In. intros y Hy. eapply (G_var_rel cenv VT_arS); eauto.
        eapply occurs_free_proj_args_args; eauto.
        intros z Hz. apply occurs_free_Eapp. now left.
    - (* Efun *)
      eapply (E_fun_compat cenv VT_arS); eauto.
      eapply (E_mono cenv VT_arS) with (k := k); [| lia ].
      eapply IHHtrans; [ solve_K |].
      eapply (G_antimon cenv VT_arS); [| eapply occurs_free_Efun_Included ].
      eapply (G_def_funs cenv VT_arS).
      + eapply (G_antimon cenv VT_arS); eauto.
        intros z [Hz Hn]. destruct Hz as [z Hz | z Hz]; [ exact Hz |].
        exfalso; apply Hn.
        match goal with
        | [ HB : trans_fundefs _ _ _ _ |- _ ] => apply (proj2 (trans_fundefs_names _ _ _ _ HB z)); exact Hz
        end.
      + eapply HG.
      + eapply HG.
      + eapply trans_fundefs_names; eauto.
      + intros f Hfn. eapply Vfun_ar; eauto.
        * eapply K_inv_def_funs; eauto.
        * eapply (G_antimon cenv VT_arS); eauto. eapply occurs_free_fundefs_Efun_Included.
    - (* Eprim_val *)
      eapply (E_stuck_compat cenv VT_arS); eauto. intros. eapply Eprim_val_stuck.
    - (* Eprim *)
      eapply (E_stuck_compat cenv VT_arS); eauto. intros. eapply Eprim_stuck.
    - (* Ehalt *)
      eapply (E_halt_compat cenv VT_arS); eauto.
      eapply (G_var_rel cenv VT_arS); eauto. fv_mem.
  Qed.

  (** ** Top level *)

  Lemma E_top_ar e e' :
    trans La (M.empty _) e e' -> E_top cenv VT_arS P PG e e'.
  Proof.
    intros Htrans k rho1 rho2 [HG _] Hbind. eapply fundamental; eauto.
    - eapply K_inv_empty.
    - eapply (G_antimon cenv VT_arS); eauto. eapply trans_occurs_free; eauto.
  Qed.

  (** Arity raising is in the λweb relation. *)
  Theorem E_web_ar e e' :
    trans La (M.empty _) e e' -> E_web cenv P PG e e'.
  Proof.
    intros Htrans. exact (E_top_E_web cenv VT_arS P PG e e' (E_top_ar e e' Htrans)).
  Qed.

End AR_rel.
