From Stdlib Require Import ZArith.
Require Import Common.
From CertiRocq Require Import
     LambdaANF.term LambdaANF.term_util LambdaANF.state LambdaANF.eval LambdaANF.shrink_cps
     LambdaANF.inline LambdaANF.uncurry_proto LambdaANF.closure_conversion
     LambdaANF.closure_conversion LambdaANF.hoisting LambdaANF.dead_param_elim LambdaANF.lambda_lifting
     LambdaANF.freshen.
From CertiRocq.LambdaBox_to_LambdaANF Require Import common.
From CertiRocq.LambdaWeb Require syntax retag dpe_impl cp_impl ar ar_impl dfn_impl hoist stats.
From MetaRocq.Utils Require MRString.
From CertiRocq.LambdaCFA Require impl fast.
From CertiRocq.LambdaBox_to_LambdaANF Require anf cps.
(* From CertiRocq.Codegen Require Import LambdaANF_to_Clight. *)

Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import ExtLib.Structures.Monad.

Import Monads.

Import MonadNotation.

Definition prim_env := M.t primitive.

Definition LambdaANFenv : Type := eval.prims * prim_env * ctor_env * ctor_tag * ind_tag * name_env * fun_env * eval.env.

Definition LambdaANFterm : Type := term.exp.
Definition LambdaANFval : Type := term.val.
Definition LambdaANF_FullTerm : Type := LambdaANFenv * LambdaANFterm.
Definition LambdaBoxEAstTerm : Type := EAst.global_declarations * EAst.term.

Section IDENT.

  Context (next_var : positive).

  Instance LambdaANF_Lang : Lang LambdaANF_FullTerm :=
    { Value := LambdaANFval;
      TermWf := fun p =>
                  let '(_, e) := p in
                  identifiers.closed_exp e /\
                  identifiers.unique_bindings e ;
      BigStep := fun p v =>
                   let '(pr, prims, cenv, ctag, itag, nenv, fenv, rho, e) := p in
                   exists c, bstep_cost pr cenv rho e v c
    }.


  (* starting tags for L5_to_LambdaANF, anything under default is reserved for special
   constructors/types *)
  Definition default_ctor_tag := 99%positive.
  Definition default_ind_tag := 99%positive.
  (* assigned for the constructor and the type of closures *)
  Definition clo_tag := 15%positive.
  Definition clo_ind_tag := 16%positive.
  (* tags for functions and continuations *)
  Definition fun_fun_tag := 3%positive.
  Definition kon_fun_tag := 2%positive.


  Definition make_prim_env (prims : list (primitive * positive)) : prim_env :=
    List.fold_left (fun map '(p, pos) => M.set pos p map) prims (M.empty _).

  Definition inductive_entry_aux_east (x : kername * EAst.global_decl) acc : common.ienv :=
    match x with
    | (s, EAst.ConstantDecl _) => acc
    | (s, EAst.InductiveDecl m) =>
      (s, ibodies_itypPack m.(ind_bodies)) :: acc
    end.

  Definition inductive_env_east (e : EAst.global_declarations) : common.ienv :=
    fold_right inductive_entry_aux_east [] e.

  Definition compile_LambdaANF_CPS prims : CertiRocqTrans LambdaBoxEAstTerm LambdaANF_FullTerm :=
    fun src =>
      debug_msg "Translating from LambdaBox (EAst) to LambdaANF (CPS)" ;;
      LiftErrorCertiRocqTrans "LambdaANF CPS"
                             (fun (p : LambdaBoxEAstTerm) =>
                                let prim_env := make_prim_env prims in
                                let ie := inductive_env_east (fst p) in
                                match cps.convert_top_cps prim_env fun_fun_tag kon_fun_tag default_ctor_tag default_ind_tag next_var
                                                          prims (fun _ => None) ie (List.rev (fst p)) (snd p) with
                                | (compM.Ret e, data) =>
                                  let (_, ctag, itag, ftag, cenv, fenv, nenv, _, _) := data in
                                  Ret (M.empty _, prim_env, cenv, ctag, itag, nenv, fenv, M.empty _, e)
                                | (compM.Err s, _) => Err s
                                end) src.

  Definition compile_LambdaANF_ANF prims : CertiRocqTrans LambdaBoxEAstTerm LambdaANF_FullTerm :=
    fun src =>
      debug_msg "Translating from LambdaBox (EAst) to LambdaANF (ANF)" ;;
      LiftErrorCertiRocqTrans "LambdaANF ANF"
                             (fun (p : LambdaBoxEAstTerm) =>
                                let prim_env := make_prim_env prims in
                                let ie := inductive_env_east (fst p) in
                                let '(_, _, _, _, dcm) :=
                                  CertiRocq.LambdaBox_to_LambdaANF.common.convert_env default_ctor_tag default_ind_tag ie in
                                match CertiRocq.LambdaBox_to_LambdaANF.anf.convert_top_anf
                                        fun_fun_tag default_ctor_tag prim_env
                                        default_ind_tag next_var dcm
                                        prims (fun _ => None) ie (List.rev (fst p)) (snd p) with
                                | (compM.Ret e, data) =>
                                  let (_, ctag, itag, ftag, cenv, fenv, nenv, _, _) := data in
                                  Ret (M.empty _, prim_env, cenv, ctag, itag, nenv, fenv, M.empty _, e)
                                | (compM.Err s, _) => Err s
                                end) src.

  (** * Definition of LambdaANF backend pipelines *)

  (* Add all names to name env *)
  Definition update_var (names : term_util.name_env) (x : var)
    : term_util.name_env :=
    match M.get x names with
    | Some (nNamed _) => names
    | Some nAnon => M.set x (nNamed "x") names
    | None => M.set x (nNamed "x") names
    end.

  Definition update_vars names xs :=
    List.fold_left update_var xs names.

  (** Adds missing names to name environment for the C translation *)
  Fixpoint add_binders_exp (names : term_util.name_env) (e : exp)
    : name_env :=
    match e with
    | Econstr x _ _ e
    | Eprim_val x _ e
    | Eprim x _ _ e
    | Eletapp x _ _ _ e
    | Eproj x _ _ _ e => add_binders_exp (update_var names x) e
    | Ecase _ pats =>
      List.fold_left (fun names p => add_binders_exp names (snd p)) pats names
    | Eapp _ _ _
    | Ehalt _ => names
    | Efun B e => add_binders_exp (add_binders_fundefs names B) e
    end
  with add_binders_fundefs (names : term_util.name_env) (B : fundefs) : term_util.name_env :=
         match B with
         | Fcons f _ xs e1 B1 =>
           add_binders_fundefs (add_binders_exp (update_vars (update_var names f) xs) e1) B1
         | Fnil => names
         end.

  Definition log_prog (e : exp) (c_data : comp_data) : comp_data :=
    match c_data with
    | mkCompData nv nc ni nf cenv fenv nenv imap log =>
      let msg := cps_show.show_exp nenv cenv false e in
      mkCompData nv nc ni nf cenv fenv nenv imap ("term" :: msg :: log)
    end.


  Record anf_options :=
    { time            : bool;    (* Keep ANF per phase timing *)
      cps             : bool;    (* CPS *)
      do_lambda_lift  : bool;    (* Do lambda lifting *)
      args            : nat;     (* Arg threshold for lambda lifting *)
      no_push         : nat;     (* *)
      inl_wrappers    : bool;    (* If true, all known calls to lambda lifted functions are inlined *)
      inl_known       : bool;    (* If true, lambda lifting inlines known calls inside wrappers *)
      inl_before      : bool;    (* Perform shrink/inline loop before closure conversion *)
      inl_after       : bool;    (* Perform shrink/inline loop after closure conversion *)
      dpe             : bool;    (* Turn it off for the top-level theorm because it does not have a proof yet *)
      webs            : bool;    (* Web optimizations: 0-CFA, then dead parameters and constants on webs *)
    }.


  Definition anf_state (A : Type) := comp_data -> error A * comp_data.


  Definition anf_trans : Type := exp -> anf_state exp.


  Global Instance MonadState : Monad anf_state :=
    { ret A x := (fun c_data  => (Ret x, c_data));
      bind A B m f :=
        (fun c_data =>
           let (a_err, c_data') := m c_data in
           match a_err with
           | Ret a => f a c_data'
           | Err s => (Err s, c_data')
           end)
    }.


  Definition id_trans : anf_trans := fun e c => (Ret e, c).

  (** Reports a message at compile time; it is the identity in Rocq, and
      prints the message in the extracted compiler. *)
  Definition web_note {A} (msg : string) (x : A) : A := x.

  Definition show_N (n : N) : string := MRString.string_of_Z (Z.of_N n).

  Definition show_stats (st0 st1 st2 : LambdaWeb.stats.stats) : string :=
    ("functions " ++ show_N (LambdaWeb.stats.n_fun st0) ++
     " (internal " ++ show_N (LambdaWeb.stats.n_fun_int st0) ++ "), calls " ++
     show_N (LambdaWeb.stats.n_call st0) ++ " (internal " ++ show_N (LambdaWeb.stats.n_call_int st0) ++
     "), constructors " ++ show_N (LambdaWeb.stats.n_con st0) ++
     " (internal " ++ show_N (LambdaWeb.stats.n_con_int st0) ++ "), uses " ++
     show_N (LambdaWeb.stats.n_use st0) ++ " (internal " ++ show_N (LambdaWeb.stats.n_use_int st0) ++
     "); DPE: parameters " ++ show_N (LambdaWeb.stats.n_param st0) ++ " -> " ++
     show_N (LambdaWeb.stats.n_param st1) ++ ", arguments " ++ show_N (LambdaWeb.stats.n_arg st0) ++
     " -> " ++ show_N (LambdaWeb.stats.n_arg st1) ++ ", bindings " ++ show_N (LambdaWeb.stats.n_bind st0) ++
     " -> " ++ show_N (LambdaWeb.stats.n_bind st1) ++ "; CP: bindings " ++
     show_N (LambdaWeb.stats.n_bind st1) ++ " -> " ++ show_N (LambdaWeb.stats.n_bind st2) ++
     ", parameters " ++ show_N (LambdaWeb.stats.n_param st1) ++ " -> " ++
     show_N (LambdaWeb.stats.n_param st2))%bs.

  (** Web optimizations: annotate the program with webs by the 0-CFA, run the
      λweb passes, and erase the webs, with fresh function tags for the
      internal webs. *)
  Definition fd_count (B : LambdaWeb.syntax.fundefs) : N :=
    N.of_nat (length (LambdaWeb.dfn_impl.fd_list B)).

  (** What defunctionalization finds: the hoisted functions, the wrappers it
      gives a tag, and the webs it selects *)
  Definition dfn_stats (cenv : ctor_env) (e : LambdaWeb.syntax.exp) : string :=
    match e with
    | LambdaWeb.syntax.Efun Btop e0 =>
        let r := LambdaWeb.dfn_impl.analyze_dfn cenv Btop e0 in
        ("top functions " ++ show_N (fd_count Btop) ++ ", wrappers " ++
         show_N (N.of_nat (length (M.elements (LambdaWeb.dfn_impl.r_tagof r)))) ++ ", selected webs " ++
         show_N (N.of_nat (length (LambdaWeb.syntax.WM_elements (LambdaWeb.dfn_impl.r_L r)))))%bs
    | _ => "no top bundle"%bs
    end.

  Definition max_key {A} (m : M.t A) : positive :=
    fold_left (fun acc p => Pos.max acc (fst p)) (M.elements m) 1%positive.

  Definition max_ind (cenv : ctor_env) : positive :=
    fold_left (fun acc p => Pos.max acc (ctor_ind_tag (snd p))) (M.elements cenv) 1%positive.

  (** Web optimizations: hoist the closed functions, annotate the program
      with webs by the 0-CFA, defunctionalize, run the other λweb passes, and
      erase the webs, with fresh function tags for the internal webs. *)
  Definition web_trans (cenv : ctor_env) : anf_trans :=
    fun e c =>
      let 'mkCompData nv nc ni nf _ fenv names imap log := c in
      let e_in := e in
      let e := LambdaWeb.hoist.hoist e in
      let w_con := LambdaWeb.syntax.Exposed 1%positive in
      let '(sl, _) := LambdaCFA.fast.analyze_fast w_con e in
      let fallback := match LambdaCFA.spec.s_ex sl with LambdaCFA.spec.AAll => true | _ => false end in
      let e0 := LambdaCFA.impl.anno w_con sl e in
      let dmsg := dfn_stats cenv e0 in
      let '(cenv', ed) := LambdaWeb.dfn_impl.dfn_top cenv e0 in
      let ndfn := (N.of_nat (length (M.elements cenv')) - N.of_nat (length (M.elements cenv)))%N in
      let La := LambdaWeb.ar_impl.ar_choose ed in
      let nflat := N.of_nat (length (filter (fun o : option LambdaWeb.ar.shape => match o with Some _ => true | None => false end)
                                            (concat (map snd (LambdaWeb.syntax.WM_elements La))))) in
      let ea := LambdaWeb.ar_impl.ar_top ed in
      let e1 := LambdaWeb.dpe_impl.dpe_top ea in
      let ew := LambdaWeb.cp_impl.cp_top e1 in
      let msg := ("Web optimizations: " ++ (if fallback then "analysis fell back to the trivial solution; " else "") ++
                  show_stats (LambdaWeb.stats.stats_of e0) (LambdaWeb.stats.stats_of e1)
                             (LambdaWeb.stats.stats_of ew) ++
                  "; defunc: " ++ dmsg ++ ", new constructors " ++ show_N ndfn ++
                  "; arity raising: webs " ++ show_N (N.of_nat (length (LambdaWeb.syntax.WM_elements La))) ++
                  ", flattened positions " ++ show_N nflat ++
                  ", parameters " ++ show_N (LambdaWeb.stats.n_param (LambdaWeb.stats.stats_of ed)) ++ " -> " ++
                  show_N (LambdaWeb.stats.n_param (LambdaWeb.stats.stats_of ea)) ++
                  ", arguments " ++ show_N (LambdaWeb.stats.n_arg (LambdaWeb.stats.stats_of ed)) ++ " -> " ++
                  show_N (LambdaWeb.stats.n_arg (LambdaWeb.stats.stats_of ea)))%bs in
      let '(e', s) := LambdaWeb.retag.erase_rt ew (LambdaWeb.retag.mk_rt (M.empty _) nf fenv) in
      let nv' := Pos.max nv (Pos.succ (identifiers.max_var e' 1%positive)) in
      let nc' := Pos.max nc (Pos.succ (max_key cenv')) in
      let ni' := Pos.max ni (Pos.succ (max_ind cenv')) in
      (* the web passes may reuse names (defunctionalization does); freshen
         the program, as the rest of the pipeline expects unique bindings.
         Freshening needs the functions of each bundle to have distinct
         names; otherwise keep the program. *)
      if freshen.fnd e' then
        web_note msg (freshen.freshen_top e' (mkCompData nv' nc' ni' (LambdaWeb.retag.rt_next s) cenv' (LambdaWeb.retag.rt_fenv s) names imap log))
      else (Ret e_in, c).

  Section Pipeline.

    Context (anf_opts : anf_options).

    Definition time_anf {A B} (name : string) (f : A -> anf_state B) : A -> anf_state B :=
      fun x s => if time anf_opts then timePhase name (f x) s else f x s.

    (* Optimizing λANF pipeline *)

    (** The passes, with the constructor environment [cenv0] for the web
        optimizations *)
    Definition anf_chain (cenv0 : ctor_env) (e : exp) : anf_state exp :=
      e <- time_anf "Shrink" shrink_err e;;
      e <- time_anf "Uncurry" (uncurry_top (cps anf_opts)) e ;;
      e <- time_anf "Inline uncurry wrappers" (inline_uncurry next_var 10 100) e ;;
      e <- (if inl_before anf_opts then
              time_anf "Inline/shrink loop" (inline_shrink_loop next_var 10 100) e
            else id_trans e) ;;
      e <- (if (do_lambda_lift anf_opts) then
              time_anf "Lambda lift" (lambda_lift (args anf_opts) (no_push anf_opts) (inl_wrappers anf_opts)) e
            else id_trans e) ;;
      e <- time_anf "Shrink" shrink_err e;;
      e <- (if webs anf_opts then
              time_anf "Web optimizations" (web_trans cenv0) e
            else id_trans e) ;;
      e <- time_anf "Closure conversion and hoisting" (closure_conversion_hoist clo_tag clo_ind_tag) e ;;
      e <- time_anf "Shrink" shrink_err e;;
      e <- (if inl_after anf_opts then
              time_anf "Inline/shrink loop" (inline_shrink_loop next_var 10 100) e
            else id_trans e) ;;
      e <- (if dpe anf_opts then
              time_anf "Dead param elim" dead_param_elim.DPE e
            else id_trans e) ;;
      e <- time_anf "Shrink" shrink_err e;;
      e <- (if inl_known anf_opts then
              time_anf "Inline known functions inside wrappers" (inline_lifted next_var 10 1000) e
            else id_trans e) ;;
      ret e.

    (** The web optimizations use the constructor environment the pipeline
        starts with, which the λANF passes before them do not change. *)
    Definition anf_pipeline (e : exp) : anf_state exp :=
      fun c0 => anf_chain (state.cenv c0) e c0.


    Definition run_anf_pipeline (t : LambdaANF_FullTerm) : error LambdaANF_FullTerm * string :=
      let '(prims, cenv, ctag, itag, nenv, fenv, _, e0) := t in
      (* make compilation state *)
      let c_data :=
          let next_var :=
              ((identifiers.max_var e0 1) + 1)%positive in
          let next_fun_tag := (M.fold (fun cm => fun ft => fun _ => Pos.max cm ft) fenv 1 + 1)%positive in
          pack_data next_var ctag itag next_fun_tag cenv fenv nenv (M.empty nat) nil
      in
      let (res, c_data') := anf_pipeline e0 c_data in
      match res with
      | compM.Err s =>
        (Err ("Failed compiling LambdaANF program: " ++ s)%bs, "")
      | compM.Ret e =>
        let (_, ctag, itag, ftag, cenv, fenv, nenv, _, log) := c_data' in
        (Ret (prims, cenv, ctag, itag, nenv, fenv, M.empty _, e), log_to_string log)
      end%positive.

  End Pipeline.


  (* ANF/Lambda-lifting Configurations for measuring performance. Passed through the anf_conf flag.

0: (DEFAULT)
   - LL: agressive inlining of wrappers at known call cites (always the known function is called)
   - do not inline  wrappers
   - fvs live across 0 calls
1: Like 0, but conservative inlining
2: Like 0, but inline known calls inside wrappers
3: Like 0, but like across 0 call
4: Like 0, but like across 2 calls
5: Like 0, but like across 10 calls
6: Like 0, but do not perform inline/shrink loop before CC
7: Like 0, but do not perform inline/shrink loop after CC
8: Like 0, but do not perform inline/shrink at all
9: Like 0, but non-selective lambda lifting
   *)

  Open Scope nat.

  Definition make_anf_options (opts : Options) : anf_options :=
    let '(inl_wrappers, inl_known, no_push, inl_before, inl_after) :=
        let default := (true, false, 1, true, true) in
        match anf_conf opts with
        | 0 => default
        | 1 => (false, false, 1, true, true)
        | 2 => (true, true, 1, true, true)
        | 3 => (true, false, 0, true, true)
        | 4 => (true, false, 2, true, true)
        | 5 => (true, false, 10, true, true)
        | 6 => (true, false, 1, false, true)
        | 7 => (true, false, 1, true, false)
        | 8 => (true, false, 1, false, false)
        | 9 => (true, false, 1000, true, true)
        | _ => default
        end
    in
    {| time := Pipeline_utils.time opts;
       cps  := negb (Pipeline_utils.direct opts);
       do_lambda_lift := (1 <=? o_level opts);
       args := if anf_conf opts =? 9 then 1000 else Pipeline_utils.c_args opts;
       no_push := no_push;
       inl_wrappers := inl_wrappers;
       inl_known    := inl_known;
       inl_before   := inl_before;
       inl_after    := inl_after;
       dpe          := true;
       webs         := (2 <=? o_level opts);
    |}.


  Definition compile_LambdaANF : CertiRocqTrans LambdaANF_FullTerm LambdaANF_FullTerm :=
    fun src =>
      debug_msg "Compiling LambdaANF" ;;
      opts <- get_options ;;
      (* Make anf_options *)
      let anf_opts := make_anf_options opts in
      LiftErrorLogCertiRocqTrans "LambdaANF Pipeline" (run_anf_pipeline anf_opts) src.


  Definition compile_LambdaANF_debug : CertiRocqTrans LambdaANF_FullTerm LambdaANF_FullTerm :=
    fun src =>
      debug_msg "Compiling LambdaANF" ;;
      opts <- get_options ;;
      (* Make anf_options *)
      let anf_opts := make_anf_options opts in
      LiftErrorLogCertiRocqTrans "LambdaANF Pipeline" (run_anf_pipeline anf_opts) src.

End IDENT.
