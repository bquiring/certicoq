(* Hoisting closed functions, before defunctionalization.

   Defunctionalization ([dfn_impl.v]) expects a program [Efun Btop e0]
   whose bundle [Btop] holds the code functions that the closures of [e0]
   wrap.  Lambda lifting produces closed code functions, but leaves them
   where they were defined.  This pass moves every bundle whose free
   variables are all functions of moved bundles to one bundle at the top of
   the program, except the bundles of wrappers.  It assumes that the bindings of the program are unique, as
   they are in the compiler's pipeline.

   The pass checks its result: the free variables of each hoisted bundle
   must be functions of the top bundle, and the program must not gain free
   variables; otherwise it returns the program unchanged.  It is proven in
   [hoist_correct.v]. *)

From Stdlib Require Import NArith.BinNat Lists.List Bool.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import set_util.
From CertiRocq.LambdaANF Require term term_util identifiers.

Import ListNotations.

Fixpoint fd_names (B : term.fundefs) : PS.t :=
  match B with
  | term.Fcons f _ _ _ B => PS.add f (fd_names B)
  | term.Fnil => PS.empty
  end.

(** All the bundles of a program, at any depth *)
Fixpoint bundles (e : term.exp) (acc : list term.fundefs) : list term.fundefs :=
  match e with
  | term.Econstr _ _ _ e | term.Eproj _ _ _ _ e | term.Eletapp _ _ _ _ e
  | term.Eprim_val _ _ e | term.Eprim _ _ _ e => bundles e acc
  | term.Ecase _ cl =>
      (fix bundles_br (cl : list (term.ctor_tag * term.exp)) (acc : list term.fundefs) :=
         match cl with
         | [] => acc
         | (_, e) :: cl => bundles_br cl (bundles e acc)
         end) cl acc
  | term.Efun B e => bundles e (bundles_fds B (B :: acc))
  | term.Eapp _ _ _ | term.Ehalt _ => acc
  end
with bundles_fds (B : term.fundefs) (acc : list term.fundefs) : list term.fundefs :=
  match B with
  | term.Fcons _ _ _ e B => bundles_fds B (bundles e acc)
  | term.Fnil => acc
  end.

(** The free variables of a bundle, other than its own functions *)
Definition bundle_fv (B : term.fundefs) : PS.t :=
  PS.diff (identifiers.fundefs_fv B) (fd_names B).

(** Wrapper bundles stay where they are: each of their functions calls a
    function of another bundle with its parameters followed by other
    arguments.  Lambda lifting makes a wrapper for each lifted function;
    defunctionalization turns the wrappers into records and dispatches to the
    hoisted code. *)
Fixpoint prefix_vars (xs ys : list term.var) : bool :=
  match xs, ys with
  | [], _ => true
  | x :: xs, y :: ys => Pos.eqb x y && prefix_vars xs ys
  | _, [] => false
  end.

Fixpoint wrappers_only (names : PS.t) (B : term.fundefs) : bool :=
  match B with
  | term.Fcons _ _ xs (term.Eapp g _ ys) B => negb (PS.mem g names) && prefix_vars xs ys && wrappers_only names B
  | term.Fcons _ _ _ _ _ => false
  | term.Fnil => true
  end.

Definition wrapper_bundle (B : term.fundefs) : bool :=
  match B with
  | term.Fnil => false
  | _ => wrappers_only (fd_names B) B
  end.

(** The bundles that can be hoisted: the greatest set of bundles whose free
    variables are functions of the set *)
Fixpoint hoistable (fuel : nat) (bs : list (PS.t * PS.t)) : list (PS.t * PS.t) :=
  match fuel with
  | O => []
  | S fuel =>
      let names := fold_left (fun acc '(ns, _) => PS.union ns acc) bs PS.empty in
      let bs' := filter (fun '(_, fv) => PS.subset fv names) bs in
      if Nat.eqb (length bs') (length bs) then bs else hoistable fuel bs'
  end.

(** The hoisted bundles, without the wrapper bundles that no other hoisted
    bundle refers to *)
Fixpoint needed_from (fuel : nat) (bs : list (PS.t * PS.t * bool)) (H : PS.t) : PS.t :=
  match fuel with
  | O => H
  | S fuel =>
      let fv := fold_left (fun acc (b : PS.t * PS.t * bool) =>
                             let '(ns, fv, _) := b in if PS.subset ns H then PS.union fv acc else acc) bs PS.empty in
      let H' := fold_left (fun acc (b : PS.t * PS.t * bool) =>
                             let '(ns, _, w) := b in
                             if w && negb (PS.is_empty (PS.inter ns fv)) then PS.union ns acc else acc) bs H in
      if PS.equal H' H then H else needed_from fuel bs H'
  end.

Definition needed (fuel : nat) (bs : list (PS.t * PS.t * bool)) : PS.t :=
  needed_from fuel bs (fold_left (fun acc (b : PS.t * PS.t * bool) =>
                                    let '(ns, _, w) := b in if w then acc else PS.union ns acc) bs PS.empty).

Section Strip.

  (** The functions of the hoisted bundles *)
  Variable (H : PS.t).

  Definition hoisted (B : term.fundefs) : bool :=
    match B with
    | term.Fcons f _ _ _ _ => PS.mem f H
    | term.Fnil => false
    end.

  (** Remove the hoisted bundles, and collect them (with their own hoisted
      bundles removed) *)
  Fixpoint strip (e : term.exp) (acc : term.fundefs) : term.exp * term.fundefs :=
    match e with
    | term.Econstr x c ys e => let '(e, acc) := strip e acc in (term.Econstr x c ys e, acc)
    | term.Eproj x c n y e => let '(e, acc) := strip e acc in (term.Eproj x c n y e, acc)
    | term.Eletapp x f t ys e => let '(e, acc) := strip e acc in (term.Eletapp x f t ys e, acc)
    | term.Eprim_val x p e => let '(e, acc) := strip e acc in (term.Eprim_val x p e, acc)
    | term.Eprim x p ys e => let '(e, acc) := strip e acc in (term.Eprim x p ys e, acc)
    | term.Ecase y cl =>
        let '(cl, acc) :=
          (fix strip_br (cl : list (term.ctor_tag * term.exp)) (acc : term.fundefs) :=
             match cl with
             | [] => ([], acc)
             | (c, e) :: cl =>
                 let '(e, acc) := strip e acc in
                 let '(cl, acc) := strip_br cl acc in
                 ((c, e) :: cl, acc)
             end) cl acc in
        (term.Ecase y cl, acc)
    | term.Efun B e =>
        let '(B', acc) := strip_fds B acc in
        let '(e, acc) := strip e acc in
        if hoisted B then (e, term_util.fundefs_append B' acc) else (term.Efun B' e, acc)
    | term.Eapp f t ys => (term.Eapp f t ys, acc)
    | term.Ehalt x => (term.Ehalt x, acc)
    end
  with strip_fds (B : term.fundefs) (acc : term.fundefs) : term.fundefs * term.fundefs :=
    match B with
    | term.Fcons f t xs e B =>
        let '(e, acc) := strip e acc in
        let '(B, acc) := strip_fds B acc in
        (term.Fcons f t xs e B, acc)
    | term.Fnil => (term.Fnil, acc)
    end.

  (** The hoisted bundles only refer to the functions [Sset] of the top
      bundle *)
  Variable (Sset : PS.t).

  Fixpoint hcheck (e : term.exp) : bool :=
    match e with
    | term.Econstr _ _ _ e | term.Eproj _ _ _ _ e | term.Eletapp _ _ _ _ e
    | term.Eprim_val _ _ e | term.Eprim _ _ _ e => hcheck e
    | term.Ecase _ cl => forallb (fun p => hcheck (snd p)) cl
    | term.Efun B e =>
        (if hoisted B then PS.subset (identifiers.fundefs_fv B) Sset else true) && hcheck_fds B && hcheck e
    | term.Eapp _ _ _ | term.Ehalt _ => true
    end
  with hcheck_fds (B : term.fundefs) : bool :=
    match B with
    | term.Fcons _ _ _ e B => hcheck e && hcheck_fds B
    | term.Fnil => true
    end.

End Strip.

Definition hoist (e : term.exp) : term.exp :=
  let bs := map (fun B => (fd_names B, bundle_fv B, wrapper_bundle B)) (bundles e []) in
  let hs := hoistable (S (length bs)) (map (fun (b : PS.t * PS.t * bool) => let '(ns, fv, _) := b in (ns, fv)) bs) in
  let H0 := fold_left (fun acc '(ns, _) => PS.union ns acc) hs PS.empty in
  let H := needed (S (length bs)) (filter (fun (b : PS.t * PS.t * bool) => let '(ns, _, _) := b in PS.subset ns H0) bs) in
  if PS.is_empty H then e else
    let '(e', Btop) := strip H e term.Fnil in
    if hcheck H (fd_names Btop) e && PS.subset (identifiers.exp_fv (term.Efun Btop e')) (identifiers.exp_fv e)
    then term.Efun Btop e' else e.
