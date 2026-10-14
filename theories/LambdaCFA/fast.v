(* A fast solver for the 0-CFA: propagating changes along dependencies.

   The solver of [impl.v] runs whole rounds over the program until nothing
   changes, so every round redoes the work of the previous ones.  Following
   "Deriving with Derivatives" (Quiring and Van Horn, ICFP 2024), this solver
   only propagates changes: it processes a worklist of small changes (new
   labels for one value set), and tracks which computations depend on which
   value sets, so that a change only reaches the computations that use it.

   The value sets are the nodes of a graph:
   - [NV x]: the flow of a variable;
   - [NA g i], [NR g]: the arguments and result of a function label;
   - [NF z i]: the fields of a constructor label;
   - [NTop]: the result of the program;
   - [NEsc]: the escaping labels, i.e. the exposed labels.

   Subset constraints are edges.  Static edges come from a walk over the
   program; dynamic edges are added when a label reaches a call site (the
   arguments flow to the parameters of the function, its result to the
   result of the call) or a projection (the field flows to the bound
   variable).  A use site becomes hot when a value of the context or an
   exposed label reaches it, after which all its labels escape (and, for a
   call, its arguments).  The labels at a use site that is not hot yet are
   recorded, so that exposing one of them later heats the site.

   The worklist only seeds the rounds of [impl.v], which continue from it
   until a fixpoint (one round when the worklist is right).  The rounds are
   proven to finish and their result to pass the checker ([check_seeded]),
   so the analysis is correct ([annotate_fast_correct]) and never falls back
   to the trivial solution ([analyze_fast_solved]), whatever the worklist
   computes. *)

From Stdlib Require Import NArith.BinNat Lists.List Bool.
Require Import compcert.lib.Coqlib.
From CertiRocq.LambdaANF Require Import set_util algebra.
From CertiRocq.LambdaANF Require term identifiers.
From CertiRocq.LambdaWeb Require Import syntax anno.
From CertiRocq.LambdaCFA Require Import spec sound impl impl_complete.

Import ListNotations.
Local Open Scope nat_scope.

(** * Nodes *)

Inductive node : Type :=
| NV (x : var)
| NA (g : var) (i : nat)
| NF (z : var) (i : nat)
| NR (g : var)
| NTop
| NEsc.

Fixpoint pairp (a : positive) (n : nat) : positive :=
  match n with O => xI a | S n => xO (pairp a n) end.

(** An injective encoding of nodes *)
Definition nkey (n : node) : positive :=
  match n with
  | NV x => xO (xO (xO x))
  | NR g => xO (xO (xI g))
  | NA g i => xO (xI (xO (pairp g i)))
  | NF z i => xO (xI (xI (pairp z i)))
  | NTop => xI xH
  | NEsc => xI (xO xH)
  end.

(** Computations that depend on the flow of a variable *)
Inductive watch : Type :=
| WCall (ys : list var) (t : node)   (* a call of the variable *)
| WProj (n : nat) (x : var).         (* a projection of the variable *)

(** * State *)

Record fs : Type :=
  mk_fs { f_v : M.t PS.t;              (* flows of variables *)
          f_r : M.t PS.t;              (* results of function labels *)
          f_a : M.t (M.t PS.t);        (* arguments of function labels, by index *)
          f_f : M.t (M.t PS.t);        (* fields of constructor labels, by index *)
          f_top : PS.t;                (* result of the program *)
          f_x : PS.t;                  (* exposed labels *)
          f_alen : M.t nat;            (* number of arguments of function labels *)
          f_flen : M.t nat;            (* number of fields of constructor labels *)
          f_edges : M.t (list node);   (* edges, by the key of their source *)
          f_watch : M.t (list watch);  (* computations depending on a variable *)
          f_site : M.t (bool * var * list var);  (* use sites: kind, subject, arguments *)
          f_vsites : M.t (list positive);        (* use sites of a variable *)
          f_nsites : positive;                   (* next use site *)
          f_hot : M.t unit;                      (* hot use sites *)
          f_lsites : M.t (list positive);        (* sites waiting for a label to be exposed *)
          f_wl : list (node * PS.t) }.           (* the worklist of changes *)

Definition empty_fs : fs :=
  mk_fs (M.empty _) (M.empty _) (M.empty _) (M.empty _) PS.empty PS.empty
        (M.empty _) (M.empty _) (M.empty _) (M.empty _) (M.empty _) (M.empty _) 1%positive
        (M.empty _) (M.empty _) [].

Definition gl2 (m : M.t (M.t PS.t)) (g : positive) (i : nat) : PS.t :=
  gv (getd m (M.empty _) g) (Pos.of_succ_nat i).

Definition sl2 (m : M.t (M.t PS.t)) (g : positive) (i : nat) (A : PS.t) : M.t (M.t PS.t) :=
  M.set g (M.set (Pos.of_succ_nat i) A (getd m (M.empty _) g)) m.

Definition getv (n : node) (s : fs) : PS.t :=
  match n with
  | NV x => gv (f_v s) x
  | NR g => gv (f_r s) g
  | NA g i => gl2 (f_a s) g i
  | NF z i => gl2 (f_f s) z i
  | NTop => f_top s
  | NEsc => f_x s
  end.

Definition setv (n : node) (A : PS.t) (s : fs) : fs :=
  let '(mk_fs v r a f top x al fl ed wa si vs ns ho ls wl) := s in
  match n with
  | NV y => mk_fs (M.set y A v) r a f top x al fl ed wa si vs ns ho ls wl
  | NR g => mk_fs v (M.set g A r) a f top x al fl ed wa si vs ns ho ls wl
  | NA g i => mk_fs v r (sl2 a g i A) f top x al fl ed wa si vs ns ho ls wl
  | NF z i => mk_fs v r a (sl2 f z i A) top x al fl ed wa si vs ns ho ls wl
  | NTop => mk_fs v r a f A x al fl ed wa si vs ns ho ls wl
  | NEsc => mk_fs v r a f top A al fl ed wa si vs ns ho ls wl
  end.

Definition with_wl (wl : list (node * PS.t)) (s : fs) : fs :=
  let '(mk_fs v r a f top x al fl ed wa si vs ns ho ls _) := s in
  mk_fs v r a f top x al fl ed wa si vs ns ho ls wl.

(** Schedule a change *)
Definition push (n : node) (A : PS.t) (s : fs) : fs :=
  if PS.is_empty A then s else with_wl ((n, A) :: f_wl s) s.

(** Add an edge, propagating what is already at its source *)
Definition add_edge (n m : node) (s : fs) : fs :=
  let '(mk_fs v r a f top x al fl ed wa si vs ns ho ls wl) := s in
  let k := nkey n in
  let s := mk_fs v r a f top x al fl (M.set k (m :: getd ed [] k) ed) wa si vs ns ho ls wl in
  push m (getv n s) s.

Definition add_watch (y : var) (w : watch) (s : fs) : fs :=
  let '(mk_fs v r a f top x al fl ed wa si vs ns ho ls wl) := s in
  mk_fs v r a f top x al fl ed (M.set y (w :: getd wa [] y) wa) si vs ns ho ls wl.

Definition add_site (fn : bool) (y : var) (ys : list var) (s : fs) : fs :=
  let '(mk_fs v r a f top x al fl ed wa si vs ns ho ls wl) := s in
  mk_fs v r a f top x al fl ed wa (M.set ns (fn, y, ys) si) (M.set y (ns :: getd vs [] y) vs)
        (Pos.succ ns) ho ls wl.

Definition set_hot (sid : positive) (s : fs) : fs :=
  let '(mk_fs v r a f top x al fl ed wa si vs ns ho ls wl) := s in
  mk_fs v r a f top x al fl ed wa si vs ns (M.set sid tt ho) ls wl.

Definition wait_label (l : lab) (sid : positive) (s : fs) : fs :=
  let '(mk_fs v r a f top x al fl ed wa si vs ns ho ls wl) := s in
  mk_fs v r a f top x al fl ed wa si vs ns ho (M.set l (sid :: getd ls [] l) ls) wl.

Definition is_hot (sid : positive) (s : fs) : bool :=
  match M.get sid (f_hot s) with Some _ => true | None => false end.

Fixpoint range (lo : nat) (n : nat) : list nat :=
  match n with O => [] | S n => lo :: range (S lo) n end.

(** Make sure that the arguments [0 .. i] of [g] exist; new arguments of an
    exposed function come from the context. *)
Definition ensure_a (g : var) (i : nat) (s : fs) : fs :=
  let n := getd (f_alen s) 0 g in
  if Nat.ltb i n then s else
    let '(mk_fs v r a f top x al fl ed wa si vs ns ho ls wl) := s in
    let s := mk_fs v r a f top x (M.set g (S i) al) fl ed wa si vs ns ho ls wl in
    if PS.mem (lfun g) (f_x s)
    then fold_left (fun s j => push (NA g j) (PS.singleton ltop) s) (range n (S i - n)) s
    else s.

(** Make sure that the fields [0 .. i] of [z] exist; new fields of an
    exposed constructor escape. *)
Definition ensure_f (z : var) (i : nat) (s : fs) : fs :=
  let n := getd (f_flen s) 0 z in
  if Nat.ltb i n then s else
    let '(mk_fs v r a f top x al fl ed wa si vs ns ho ls wl) := s in
    let s := mk_fs v r a f top x al (M.set z (S i) fl) ed wa si vs ns ho ls wl in
    if PS.mem (lcon z) (f_x s)
    then fold_left (fun s j => add_edge (NF z j) NEsc s) (range n (S i - n)) s
    else s.

(** A use site gets hot: its labels and its arguments escape. *)
Definition heat (sid : positive) (s : fs) : fs :=
  if is_hot sid s then s else
    match M.get sid (f_site s) with
    | Some (fn, y, ys) =>
        let s := set_hot sid s in
        let s := push NEsc (kind_labels fn (gv (f_v s) y)) s in
        fold_left (fun s y => add_edge (NV y) NEsc s) ys s
    | None => s
    end.

(** A label gets exposed (it is already in [f_x]). *)
Definition expose (l : lab) (s : fs) : fs :=
  let s := match l with
           | xO g =>
               let s := add_edge (NR g) NEsc s in
               fold_left (fun s j => push (NA g j) (PS.singleton ltop) s)
                         (range 0 (getd (f_alen s) 0 g)) s
           | xI z =>
               fold_left (fun s j => add_edge (NF z j) NEsc s) (range 0 (getd (f_flen s) 0 z)) s
           | xH => s
           end in
  fold_left (fun s sid => heat sid s) (getd (f_lsites s) [] l) s.

(** New labels [D] for the flow of [y] *)
Definition run_watch (D : PS.t) (s : fs) (w : watch) : fs :=
  match w with
  | WCall ys t =>
      PS.fold (fun l s =>
                 match l with
                 | xO g =>
                     let s := fold_i (fun s i y => add_edge (NV y) (NA g i) (ensure_a g i s)) 0 ys s in
                     add_edge (NR g) t s
                 | xH => push t (PS.singleton ltop) s
                 | _ => s
                 end) D s
  | WProj n x =>
      PS.fold (fun l s =>
                 match l with
                 | xI z => add_edge (NF z n) (NV x) s
                 | xH => push (NV x) (PS.singleton ltop) s
                 | _ => s
                 end) D s
  end.

Definition run_site (D : PS.t) (s : fs) (sid : positive) : fs :=
  match M.get sid (f_site s) with
  | Some (fn, y, _) =>
      let K := kind_labels fn D in
      if is_hot sid s then push NEsc K s
      else if PS.mem ltop D || negb (PS.is_empty (PS.inter K (f_x s))) then heat sid s
      else PS.fold (fun l s => wait_label l sid s) K s
  | None => s
  end.

(** Process a change [D] to the node [n] *)
Definition process (n : node) (D : PS.t) (s : fs) : fs :=
  let D := match n with NEsc => PS.remove ltop D | _ => D end in
  let D := PS.diff D (getv n s) in
  if PS.is_empty D then s else
    let s := setv n (PS.union (getv n s) D) s in
    let s := fold_left (fun s m => push m D s) (getd (f_edges s) [] (nkey n)) s in
    match n with
    | NEsc => PS.fold expose D s
    | NV y =>
        let s := fold_left (run_watch D) (getd (f_watch s) [] y) s in
        fold_left (run_site D) (getd (f_vsites s) [] y) s
    | _ => s
    end.

Definition step1 (s : fs) : fs :=
  match f_wl s with
  | [] => s
  | (n, D) :: wl => process n D (with_wl wl s)
  end.

(** * The constraints of the program *)

Fixpoint gen (cur : node) (e : term.exp) (s : fs) : fs :=
  match e with
  | term.Econstr x c ys e =>
      let s := push (NV x) (PS.singleton (lcon x)) s in
      let s := fold_i (fun s i y => add_edge (NV y) (NF x i) (ensure_f x i s)) 0 ys s in
      gen cur e s
  | term.Ecase y cl =>
      let s := add_site false y [] s in
      (fix gen_br (cl : list (term.ctor_tag * term.exp)) (s : fs) :=
         match cl with
         | [] => s
         | (_, e) :: cl => gen_br cl (gen cur e s)
         end) cl s
  | term.Eproj x c n y e =>
      let s := add_site false y [] s in
      let s := add_watch y (WProj (N.to_nat n) x) s in
      gen cur e s
  | term.Eletapp x f t ys e =>
      let s := add_site true f ys s in
      let s := add_watch f (WCall ys (NV x)) s in
      gen cur e s
  | term.Efun B e => gen cur e (gen_fds B s)
  | term.Eapp f t ys =>
      let s := add_site true f ys s in
      add_watch f (WCall ys cur) s
  | term.Eprim_val x p e => gen cur e s
  | term.Eprim x p ys e => gen cur e s
  | term.Ehalt x => add_edge (NV x) cur s
  end
with gen_fds (B : term.fundefs) (s : fs) : fs :=
  match B with
  | term.Fcons g t xs b B =>
      let s := push (NV g) (PS.singleton (lfun g)) s in
      let s := fold_i (fun s i x => add_edge (NA g i) (NV x) (ensure_a g i s)) 0 xs s in
      gen_fds B (gen (NR g) b s)
  | term.Fnil => s
  end.

Definition init_fs (e : term.exp) : fs :=
  let s := gen NTop e empty_fs in
  let s := add_edge NTop NEsc s in
  fold_left (fun s x => push (NV x) (PS.singleton ltop) s) (PS.elements (identifiers.exp_fv e)) s.

(** * The seed *)

Definition lists_of (len : M.t nat) (m : M.t (M.t PS.t)) : M.t (list PS.t) :=
  M.map (fun g n => map (fun i => gl2 m g i) (range 0 n)) len.

Definition st_of (s : fs) : st :=
  mk_st (f_v s) (lists_of (f_alen s) (f_a s)) (lists_of (f_flen s) (f_f s)) (f_r s) (f_top s) (f_x s).

(** Fuel: one change per step, up to 2^50 steps *)
Definition fast_fuel : positive := Pos.pow 2 50.

(** The state reached by the worklist; it is only a seed, so running out of
    fuel is not a problem. *)
Definition fast_seed (e : term.exp) : st :=
  match loop step1 (fun _ s' => match f_wl s' with [] => true | _ => false end) fast_fuel (init_fs e) with
  | Done s | More s => st_of s
  end.

(** * The analysis *)

Section Analysis.

  Variable (w_con : web).
  Hypothesis (Hw_con : exposedb w_con = true).

  (** The rounds of [impl.v] continue from the seed until a fixpoint, so the
      result is a fixpoint whatever the worklist computed; when the worklist
      is right, this takes one round. *)
  Definition analyze_fast (e : term.exp) : sol * aset :=
    match solve_seeded e (fast_seed e) with
    | Done fin => let '(s, R) := sol_of e fin in if check w_con s R e then (s, R) else (triv, AAll)
    | More _ => (triv, AAll)
    end.

  Definition annotate_fast (e : term.exp) : exp :=
    let '(s, _) := analyze_fast e in anno w_con s e.

  Lemma analyze_fast_ok e : let '(s, R) := analyze_fast e in ok_top w_con s R e (anno w_con s e).
  Proof.
    unfold analyze_fast. destruct (solve_seeded e (fast_seed e)) as [fin | fin]; [| eapply triv_top ].
    destruct (sol_of e fin) as [s R].
    destruct (check w_con s R e) eqn:Hc; [ eapply check_spec; eauto | eapply triv_top ].
  Qed.

  (** The analysis never falls back to the trivial solution. *)
  Theorem analyze_fast_solved e :
    exists fin, solve_seeded e (fast_seed e) = Done fin /\ analyze_fast e = sol_of e fin.
  Proof.
    destruct (solve_seeded_done e (fast_seed e)) as [fin HS]. exists fin. split; [ exact HS |].
    unfold analyze_fast. rewrite HS. pose proof (check_seeded w_con e (fast_seed e) fin HS) as Hc.
    destruct (sol_of e fin) as [s R]. simpl in Hc. rewrite Hc. reflexivity.
  Qed.

  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.

  (** The analysis inhabits the annotation relation. *)
  Theorem annotate_fast_correct cenv e :
    E_anno_top cenv w_con (P_eq (fuel := fuel) (trace := trace)) P_eq e (annotate_fast e).
  Proof.
    unfold annotate_fast. pose proof (analyze_fast_ok e) as Hok.
    destruct (analyze_fast e) as [s R]. eapply ok_top_E_anno; eauto.
  Qed.

End Analysis.
