(* Hoisting closed functions, before defunctionalization.

   Defunctionalization ([dfn_impl.v]) expects a program [Efun Btop e0]
   whose bundle [Btop] holds the code functions that the closures of [e0]
   wrap.  Lambda lifting produces closed code functions, but leaves them
   where they were defined.  This pass moves every bundle whose free
   variables are all functions of moved bundles to one bundle at the top of
   the program.  It assumes that the bindings of the program are unique, as
   they are in the compiler's pipeline.

   This pass is not proven yet. *)

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

End Strip.

Definition hoist (e : term.exp) : term.exp :=
  let bs := map (fun B => (fd_names B, bundle_fv B)) (bundles e []) in
  let hs := hoistable (S (length bs)) bs in
  let H := fold_left (fun acc '(ns, _) => PS.union ns acc) hs PS.empty in
  if PS.is_empty H then e else
    let '(e', Btop) := strip H e term.Fnil in
    term.Efun Btop e'.
