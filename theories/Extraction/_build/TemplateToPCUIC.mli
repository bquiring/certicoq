open Ast0
open BasicAst
open Datatypes
open List0
open PCUICAst
open PCUICAstUtils
open UGraph0
open Univ0
open Utils

module T :
 sig
  type term = Ast0.term =
  | Coq_tRel of nat
  | Coq_tVar of ident
  | Coq_tMeta of nat
  | Coq_tEvar of nat * term list
  | Coq_tSort of universe
  | Coq_tCast of term * cast_kind * term
  | Coq_tProd of name * term * term
  | Coq_tLambda of name * term * term
  | Coq_tLetIn of name * term * term * term
  | Coq_tApp of term * term list
  | Coq_tConst of kername * universe_instance
  | Coq_tInd of inductive * universe_instance
  | Coq_tConstruct of inductive * nat * universe_instance
  | Coq_tCase of (inductive * nat) * term * term * (nat * term) list
  | Coq_tProj of projection * term
  | Coq_tFix of term mfixpoint * nat
  | Coq_tCoFix of term mfixpoint * nat

  val term_rect :
    (nat -> 'a1) -> (ident -> 'a1) -> (nat -> 'a1) -> (nat -> term list ->
    'a1) -> (universe -> 'a1) -> (term -> 'a1 -> cast_kind -> term -> 'a1 ->
    'a1) -> (name -> term -> 'a1 -> term -> 'a1 -> 'a1) -> (name -> term ->
    'a1 -> term -> 'a1 -> 'a1) -> (name -> term -> 'a1 -> term -> 'a1 -> term
    -> 'a1 -> 'a1) -> (term -> 'a1 -> term list -> 'a1) -> (kername ->
    universe_instance -> 'a1) -> (inductive -> universe_instance -> 'a1) ->
    (inductive -> nat -> universe_instance -> 'a1) -> ((inductive * nat) ->
    term -> 'a1 -> term -> 'a1 -> (nat * term) list -> 'a1) -> (projection ->
    term -> 'a1 -> 'a1) -> (term mfixpoint -> nat -> 'a1) -> (term mfixpoint
    -> nat -> 'a1) -> term -> 'a1

  val term_rec :
    (nat -> 'a1) -> (ident -> 'a1) -> (nat -> 'a1) -> (nat -> term list ->
    'a1) -> (universe -> 'a1) -> (term -> 'a1 -> cast_kind -> term -> 'a1 ->
    'a1) -> (name -> term -> 'a1 -> term -> 'a1 -> 'a1) -> (name -> term ->
    'a1 -> term -> 'a1 -> 'a1) -> (name -> term -> 'a1 -> term -> 'a1 -> term
    -> 'a1 -> 'a1) -> (term -> 'a1 -> term list -> 'a1) -> (kername ->
    universe_instance -> 'a1) -> (inductive -> universe_instance -> 'a1) ->
    (inductive -> nat -> universe_instance -> 'a1) -> ((inductive * nat) ->
    term -> 'a1 -> term -> 'a1 -> (nat * term) list -> 'a1) -> (projection ->
    term -> 'a1 -> 'a1) -> (term mfixpoint -> nat -> 'a1) -> (term mfixpoint
    -> nat -> 'a1) -> term -> 'a1

  val mkApps : term -> term list -> term

  val mkApp : term -> term -> term

  val isApp : term -> bool

  val isLambda : term -> bool

  type parameter_entry = Ast0.parameter_entry = { parameter_entry_type : 
                                                  term;
                                                  parameter_entry_universes : 
                                                  universe_context }

  val parameter_entry_type : parameter_entry -> term

  val parameter_entry_universes : parameter_entry -> universe_context

  type definition_entry = Ast0.definition_entry = { definition_entry_type : 
                                                    term;
                                                    definition_entry_body : 
                                                    term;
                                                    definition_entry_universes : 
                                                    universe_context;
                                                    definition_entry_opaque : 
                                                    bool }

  val definition_entry_type : definition_entry -> term

  val definition_entry_body : definition_entry -> term

  val definition_entry_universes : definition_entry -> universe_context

  val definition_entry_opaque : definition_entry -> bool

  type constant_entry = Ast0.constant_entry =
  | ParameterEntry of parameter_entry
  | DefinitionEntry of definition_entry

  val constant_entry_rect :
    (parameter_entry -> 'a1) -> (definition_entry -> 'a1) -> constant_entry
    -> 'a1

  val constant_entry_rec :
    (parameter_entry -> 'a1) -> (definition_entry -> 'a1) -> constant_entry
    -> 'a1

  type recursivity_kind = Ast0.recursivity_kind =
  | Finite
  | CoFinite
  | BiFinite

  val recursivity_kind_rect : 'a1 -> 'a1 -> 'a1 -> recursivity_kind -> 'a1

  val recursivity_kind_rec : 'a1 -> 'a1 -> 'a1 -> recursivity_kind -> 'a1

  type local_entry = Ast0.local_entry =
  | LocalDef of term
  | LocalAssum of term

  val local_entry_rect : (term -> 'a1) -> (term -> 'a1) -> local_entry -> 'a1

  val local_entry_rec : (term -> 'a1) -> (term -> 'a1) -> local_entry -> 'a1

  type one_inductive_entry = Ast0.one_inductive_entry = { mind_entry_typename : 
                                                          ident;
                                                          mind_entry_arity : 
                                                          term;
                                                          mind_entry_template : 
                                                          bool;
                                                          mind_entry_consnames : 
                                                          ident list;
                                                          mind_entry_lc : 
                                                          term list }

  val mind_entry_typename : one_inductive_entry -> ident

  val mind_entry_arity : one_inductive_entry -> term

  val mind_entry_template : one_inductive_entry -> bool

  val mind_entry_consnames : one_inductive_entry -> ident list

  val mind_entry_lc : one_inductive_entry -> term list

  type mutual_inductive_entry = Ast0.mutual_inductive_entry = { mind_entry_record : 
                                                                ident option
                                                                option;
                                                                mind_entry_finite : 
                                                                recursivity_kind;
                                                                mind_entry_params : 
                                                                (ident * local_entry)
                                                                list;
                                                                mind_entry_inds : 
                                                                one_inductive_entry
                                                                list;
                                                                mind_entry_universes : 
                                                                universe_context;
                                                                mind_entry_private : 
                                                                bool option }

  val mind_entry_record : mutual_inductive_entry -> ident option option

  val mind_entry_finite : mutual_inductive_entry -> recursivity_kind

  val mind_entry_params : mutual_inductive_entry -> (ident * local_entry) list

  val mind_entry_inds : mutual_inductive_entry -> one_inductive_entry list

  val mind_entry_universes : mutual_inductive_entry -> universe_context

  val mind_entry_private : mutual_inductive_entry -> bool option

  type context_decl = Ast0.context_decl = { decl_name : name;
                                            decl_body : term option;
                                            decl_type : term }

  val decl_name : context_decl -> name

  val decl_body : context_decl -> term option

  val decl_type : context_decl -> term

  val vass : name -> term -> context_decl

  val vdef : name -> term -> term -> context_decl

  type context = context_decl list

  val snoc : 'a1 list -> 'a1 -> 'a1 list

  type one_inductive_body = Ast0.one_inductive_body = { ind_name : ident;
                                                        ind_type : term;
                                                        ind_kelim : sort_family
                                                                    list;
                                                        ind_ctors : ((ident * term) * nat)
                                                                    list;
                                                        ind_projs : (ident * term)
                                                                    list }

  val ind_name : one_inductive_body -> ident

  val ind_type : one_inductive_body -> term

  val ind_kelim : one_inductive_body -> sort_family list

  val ind_ctors : one_inductive_body -> ((ident * term) * nat) list

  val ind_projs : one_inductive_body -> (ident * term) list

  type mutual_inductive_body = Ast0.mutual_inductive_body = { ind_npars : 
                                                              nat;
                                                              ind_params : 
                                                              context;
                                                              ind_bodies : 
                                                              one_inductive_body
                                                              list;
                                                              ind_universes : 
                                                              universe_context }

  val ind_npars : mutual_inductive_body -> nat

  val ind_params : mutual_inductive_body -> context

  val ind_bodies : mutual_inductive_body -> one_inductive_body list

  val ind_universes : mutual_inductive_body -> universe_context

  type constant_body = Ast0.constant_body = { cst_type : term;
                                              cst_body : term option;
                                              cst_universes : universe_context }

  val cst_type : constant_body -> term

  val cst_body : constant_body -> term option

  val cst_universes : constant_body -> universe_context

  type global_decl = Ast0.global_decl =
  | ConstantDecl of kername * constant_body
  | InductiveDecl of kername * mutual_inductive_body

  val global_decl_rect :
    (kername -> constant_body -> 'a1) -> (kername -> mutual_inductive_body ->
    'a1) -> global_decl -> 'a1

  val global_decl_rec :
    (kername -> constant_body -> 'a1) -> (kername -> mutual_inductive_body ->
    'a1) -> global_decl -> 'a1

  type global_declarations = global_decl list

  type global_context = global_declarations * t

  type program = global_declarations * term
 end

val trans : T.term -> term

val trans_decl : T.context_decl -> context_decl

val trans_local : T.context_decl list -> context_decl list

val trans_one_ind_body : T.one_inductive_body -> one_inductive_body

val trans_constant_body : T.constant_body -> constant_body

val trans_minductive_body : T.mutual_inductive_body -> mutual_inductive_body

val trans_global_decl : T.global_decl -> global_decl

val trans_global_decls : T.global_decl list -> global_decl list

val trans_global : T.global_context -> global_decl list * t
