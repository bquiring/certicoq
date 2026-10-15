(* A constraint solver, and the flow analyses of the λweb passes built on it.

   * The solver

   A problem is a list of constraints [k ⊒ t] over a join semi-lattice
   [(A, bot, join)], where [k] is a key and [t] is a constant or the value
   of a key.  The solver computes the least solution by round-robin
   iteration: it applies every constraint in turn ([round]), and repeats
   until a round changes nothing.

   Expected correctness (not yet proven; the passes do not rely on it, as
   they check the results of their analyses): if [eqb] decides equality,
   [join] is a join semi-lattice with least element [bot], and no chain of
   [A] has more than [h + 1] elements, then [solve h cs] returns [Some s],
   and [s] is the least map satisfying every constraint of [cs].  A round
   that changes the map raises the value of a key, which can happen at most
   [h] times per key, and only the targets of constraints change, so at
   most [h * length cs] rounds change the map, and the fuel suffices.

   * The analyses

   The keys are the variables of a program and the parameter positions of
   its webs.  Each analysis generates one constraint per flow:

   - Liveness (for dead parameter elimination), over booleans: a variable is
     live if a case analyzes it, a primitive or [halt] uses it, a call calls
     it, or it flows into a live variable or parameter position; a parameter
     position is live if the parameter of some function of the web is.  A
     parameter that is only passed on to the same position of a recursive
     call stays dead.
   - Known constructors (for arity raising and constant propagation), over
     the flat lattice of constructor shapes: a variable bound by [Econstr]
     holds that constructor, a parameter holds what its position receives,
     and a position receives the arguments of all calls of the web.

   Webs whose functions disagree on their arity, or have repeated
   parameters, and exposed webs, are not transformed: their positions are
   live and unknown. *)

From Stdlib Require Import NArith.BinNat Lists.List Bool.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaWeb Require Import syntax.

Import ListNotations.

(** * The solver *)

Section Solver.

  Context {A : Type} (bot : A) (join : A -> A -> A) (eqb : A -> A -> bool).

  Inductive term : Type :=
  | Const (a : A)
  | Look (k : positive).

  (** [(k, t)]: the value of [k] is at least [t] *)
  Definition constr : Type := positive * term.

  Definition get (s : M.t A) (k : positive) : A :=
    match s ! k with Some a => a | None => bot end.

  Definition eval (s : M.t A) (t : term) : A :=
    match t with Const a => a | Look k => get s k end.

  (** Apply a constraint; the flag records a change *)
  Definition update (sc : M.t A * bool) (c : constr) : M.t A * bool :=
    let '(s, ch) := sc in
    let '(k, t) := c in
    let old := get s k in
    let nw := join old (eval s t) in
    if eqb nw old then (s, ch) else (M.set k nw s, true).

  Definition round (cs : list constr) (s : M.t A) : M.t A * bool :=
    fold_left update cs (s, false).

  Fixpoint iterate (fuel : nat) (cs : list constr) (s : M.t A) : option (M.t A) :=
    match fuel with
    | O => None
    | S fuel =>
        let '(s', ch) := round cs s in
        if ch then iterate fuel cs s' else Some s'
    end.

  (** [h]: the height of the lattice *)
  Definition solve (h : nat) (cs : list constr) : option (M.t A) :=
    iterate (S (h * length cs)) cs (M.empty A).

End Solver.

Arguments term : clear implicits.
Arguments constr : clear implicits.

(** * Lattices *)

(** Constructor shapes: none yet, a constructor of web [w] with tag [c] and
    [n] fields, or several *)
Inductive cval : Type :=
| CBot
| CCon (w : web) (c : ctor_tag) (n : nat)
| CTop.

Definition cval_eqb (a b : cval) : bool :=
  match a, b with
  | CBot, CBot | CTop, CTop => true
  | CCon w c n, CCon w' c' n' => web_eqb w w' && Pos.eqb c c' && Nat.eqb n n'
  | _, _ => false
  end.

Definition cval_join (a b : cval) : cval :=
  match a, b with
  | CBot, b => b
  | a, CBot => a
  | CCon _ _ _, CCon _ _ _ => if cval_eqb a b then a else CTop
  | _, _ => CTop
  end.

(** * Keys *)

Fixpoint shiftz (n : nat) (t : positive) : positive :=
  match n with
  | O => t
  | S n => xO (shiftz n t)
  end.

(** [emb p k]: the bits of [p], each preceded by a zero, then a one, then
    [k]; injective in [p] and [k] *)
Fixpoint emb (p k : positive) : positive :=
  match p with
  | xO p => xO (xO (emb p k))
  | xI p => xO (xI (emb p k))
  | xH => xI k
  end.

Definition wcode (w : web) : positive := match w with Internal p => xO p | Exposed t => xI t end.

Definition kvar (x : var) : positive := xO x.

(** The [i]-th parameter position of web [w] *)
Definition kparam (w : web) (i : nat) : positive := xI (xI (emb (wcode w) (Pos.of_succ_nat i))).

Definition imap {B C} (f : nat -> B -> C) (l : list B) : list C :=
  map (fun p => f (fst p) (snd p)) (combine (seq 0 (length l)) l).

(** * The webs that are transformed *)

Fixpoint nodupb (xs : list var) : bool :=
  match xs with
  | [] => true
  | x :: xs => negb (existsb (Pos.eqb x) xs) && nodupb xs
  end.

(** The arity of the functions of each web, [None] if they disagree or
    have repeated parameters *)
Definition add_arity (w : web) (xs : list var) (tbl : WM.t (option nat)) : WM.t (option nat) :=
  if nodupb xs then
    match WM.get w tbl with
    | None => WM.set w (Some (length xs)) tbl
    | Some None => tbl
    | Some (Some n) => if Nat.eqb n (length xs) then tbl else WM.set w None tbl
    end
  else WM.set w None tbl.

Fixpoint arities (e : exp) (tbl : WM.t (option nat)) : WM.t (option nat) :=
  match e with
  | Econstr _ _ _ _ k | Eproj _ _ _ _ _ k | Eletapp _ _ _ _ k
  | Eprim_val _ _ k | Eprim _ _ _ k => arities k tbl
  | Ecase _ _ cl =>
      (fix go (cl : list (ctor_tag * exp)) tbl :=
         match cl with
         | [] => tbl
         | (_, e) :: cl => go cl (arities e tbl)
         end) cl tbl
  | Efun B k => arities k (arities_fd B tbl)
  | Eapp _ _ _ | Ehalt _ => tbl
  end
with arities_fd (B : fundefs) (tbl : WM.t (option nat)) : WM.t (option nat) :=
  match B with
  | Fcons _ w xs e B => arities_fd B (arities e (add_arity w xs tbl))
  | Fnil => tbl
  end.

Section Analyses.

  Variable (ar : WM.t (option nat)).

  (** The webs whose positions are tracked *)
  Definition okw (w : web) : bool :=
    negb (exposedb w) && match WM.get w ar with Some (Some _) => true | _ => false end.

  (** ** Liveness *)

  Definition live_call (f : var) (w : web) (ys : list var) : list (constr bool) :=
    (kvar f, Const true) ::
    (if okw w then imap (fun i y => (kvar y, Look (kparam w i))) ys
     else map (fun y => (kvar y, Const true)) ys).

  Fixpoint live_cs (e : exp) (acc : list (constr bool)) : list (constr bool) :=
    match e with
    | Econstr x _ _ ys k => live_cs k (map (fun y => (kvar y, Look (kvar x))) ys ++ acc)
    | Eproj x _ _ _ y k => live_cs k ((kvar y, Look (kvar x)) :: acc)
    | Ecase x _ cl =>
        (fix go (cl : list (ctor_tag * exp)) acc :=
           match cl with
           | [] => acc
           | (_, e) :: cl => go cl (live_cs e acc)
           end) cl ((kvar x, Const true) :: acc)
    | Eletapp _ f w ys k => live_cs k (live_call f w ys ++ acc)
    | Efun B k => live_cs k (live_cs_fd B acc)
    | Eapp f w ys => live_call f w ys ++ acc
    | Eprim_val _ _ k => live_cs k acc
    | Eprim _ _ ys k => live_cs k (map (fun y => (kvar y, Const true)) ys ++ acc)
    | Ehalt x => (kvar x, Const true) :: acc
    end
  with live_cs_fd (B : fundefs) (acc : list (constr bool)) : list (constr bool) :=
    match B with
    | Fcons _ w xs e B =>
        let ps := if okw w then imap (fun i x => (kparam w i, Look (kvar x))) xs
                  else imap (fun i _ => (kparam w i, Const true)) xs in
        live_cs_fd B (live_cs e (ps ++ acc))
    | Fnil => acc
    end.

  (** ** Known constructors *)

  Definition con_call (w : web) (ys : list var) : list (constr cval) :=
    if okw w then imap (fun i y => (kparam w i, Look (kvar y))) ys else [].

  Fixpoint con_cs (e : exp) (acc : list (constr cval)) : list (constr cval) :=
    match e with
    | Econstr x w c ys k => con_cs k ((kvar x, Const (CCon w c (length ys))) :: acc)
    | Eproj x _ _ _ _ k | Eprim_val x _ k | Eprim x _ _ k => con_cs k ((kvar x, Const CTop) :: acc)
    | Ecase _ _ cl =>
        (fix go (cl : list (ctor_tag * exp)) acc :=
           match cl with
           | [] => acc
           | (_, e) :: cl => go cl (con_cs e acc)
           end) cl acc
    | Eletapp x _ w ys k => con_cs k ((kvar x, Const CTop) :: con_call w ys ++ acc)
    | Efun B k => con_cs k (con_cs_fd B acc)
    | Eapp _ w ys => con_call w ys ++ acc
    | Ehalt _ => acc
    end
  with con_cs_fd (B : fundefs) (acc : list (constr cval)) : list (constr cval) :=
    match B with
    | Fcons f w xs e B =>
        let ps := if okw w then imap (fun i x => (kvar x, Look (kparam w i))) xs
                  else map (fun x => (kvar x, Const CTop)) xs in
        con_cs_fd B (con_cs e ((kvar f, Const CTop) :: ps ++ acc))
    | Fnil => acc
    end.

End Analyses.

(** * Results *)

(** The tracked webs and their arities *)
Definition tracked (e : exp) : list (web * nat) :=
  let ar := arities e (WM.empty _) in
  flat_map (fun '(w, o) => match o with
                           | Some n => if okw ar w then [(w, n)] else []
                           | None => []
                           end) (WM_elements ar).

(** For every tracked web, which parameters are live *)
Definition live_masks (e : exp) : option (WM.t (list bool)) :=
  let ar := arities e (WM.empty _) in
  match solve false orb Bool.eqb 1 (live_cs ar e []) with
  | Some s =>
      Some (fold_left (fun L '(w, n) => WM.set w (map (fun i => get false s (kparam w i)) (seq 0 n)) L)
                      (tracked e) (WM.empty _))
  | None => None
  end.

(** For every tracked web, the constructor shape each parameter receives.
    A position that receives nothing (its web is never called) is unknown:
    its parameters may still be passed on, and a transformation needs a
    shape for them.  Marking these positions unknown only raises values, so
    a second solution has no such positions left. *)
Definition param_cons (e : exp) : option (WM.t (list cval)) :=
  let ar := arities e (WM.empty _) in
  let cs := con_cs ar e [] in
  let tr := tracked e in
  let table s := fold_left (fun L '(w, n) => WM.set w (map (fun i => get CBot s (kparam w i)) (seq 0 n)) L)
                           tr (WM.empty _) in
  match solve CBot cval_join cval_eqb 2 cs with
  | Some s =>
      let never := flat_map (fun '(w, n) => flat_map (fun i => match get CBot s (kparam w i) with
                                                               | CBot => [(kparam w i, Const CTop)]
                                                               | _ => []
                                                               end) (seq 0 n)) tr in
      match solve CBot cval_join cval_eqb 2 (never ++ cs) with
      | Some s => Some (table s)
      | None => None
      end
  | None => None
  end.

(** ** Records that are only projected

    Arity raising rebuilds a flattened record on function entry, which
    allocates unless every use of the record is a projection or a case
    analysis, which the λANF shrinker resolves once the record is known.  A
    variable escapes (true) if it is used otherwise: stored in a
    constructor, used by a primitive or [halt], or passed at a position that
    is not flattened.  Passing it at a flattened position
    projects its fields, so it escapes only if that position does.  A
    position escapes if a parameter at that position does.  [flat w i]: the
    positions that may be flattened. *)

Section Escape.

  Variables (ar : WM.t (option nat)) (flat : web -> nat -> bool).

  Definition esc_call (f : var) (w : web) (ys : list var) : list (constr bool) :=
    (kvar f, Const true) ::
    imap (fun i y => if okw ar w && flat w i then (kvar y, Look (kparam w i)) else (kvar y, Const true)) ys.

  Fixpoint esc_cs (e : exp) (acc : list (constr bool)) : list (constr bool) :=
    match e with
    | Econstr _ _ _ ys k => esc_cs k (map (fun y => (kvar y, Const true)) ys ++ acc)
    | Eproj _ _ _ _ _ k | Eprim_val _ _ k => esc_cs k acc
    | Ecase _ _ cl =>
        (fix go (cl : list (ctor_tag * exp)) acc :=
           match cl with
           | [] => acc
           | (_, e) :: cl => go cl (esc_cs e acc)
           end) cl acc
    | Eletapp _ f w ys k => esc_cs k (esc_call f w ys ++ acc)
    | Efun B k => esc_cs k (esc_cs_fd B acc)
    | Eapp f w ys => esc_call f w ys ++ acc
    | Eprim _ _ ys k => esc_cs k (map (fun y => (kvar y, Const true)) ys ++ acc)
    | Ehalt x => (kvar x, Const true) :: acc
    end
  with esc_cs_fd (B : fundefs) (acc : list (constr bool)) : list (constr bool) :=
    match B with
    | Fcons _ w xs e B =>
        let ps := if okw ar w then imap (fun i x => (kparam w i, Look (kvar x))) xs else [] in
        esc_cs_fd B (esc_cs e (ps ++ acc))
    | Fnil => acc
    end.

End Escape.

(** For every tracked web, which positions escape *)
Definition escaping (e : exp) (flat : web -> nat -> bool) : option (WM.t (list bool)) :=
  let ar := arities e (WM.empty _) in
  match solve false orb Bool.eqb 1 (esc_cs ar flat e []) with
  | Some s =>
      Some (fold_left (fun L '(w, n) => WM.set w (map (fun i => get false s (kparam w i)) (seq 0 n)) L)
                      (tracked e) (WM.empty _))
  | None => None
  end.
