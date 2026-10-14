# λweb: flow-directed transformations for CertiRocq

This directory adapts *Compositional Verification of Flow-directed
Transformations* (the λweb development) to CertiRocq's λANF.  Compared to the
paper's standalone mechanization, it

* builds on CertiRocq's actual λANF: mutually recursive function bundles,
  primitive values, `Ehalt`, `caseConsistent`, and the abstract fuel/trace
  resource algebra of `LambdaANF/algebra.v`;
* generalizes every logical relation with CertiRocq's postconditions: a local
  postcondition `P` on expression relations and a global postcondition `PG`
  on value relations (`LambdaANF/logical_relations.v`), with the
  corresponding closure obligations (`Post_properties`) and
  `post_upper_bound` for divergence preservation;
* reuses CertiRocq's function tags as function webs (λANF already checks them
  at every call), adding webs only to constructors, projections and case
  analyses.

The analysis phase is specified by the annotation relation (`anno.v`) and
assumed in `pipeline.v`; a compositional 0-CFA inhabiting it is in
`../LambdaCFA` (see its `STRUCTURE.md`).

## Files

| File | Contents | Paper |
| :--- | :--- | :--- |
| `syntax.v` | λweb syntax and values, webs (`Exposed p` / `Internal p`) and maps indexed by webs (`WM`), exposed and well-formed values, erasure to λANF, free variables (inherited through erasure) | Fig. 3, Fig. 4 (top) |
| `semantics.v` | Fuel/trace big-step semantics with web and exposure checks; determinism, fuel lemmas, preservation of well-formedness | Fig. 4, Lemma 4.1 |
| `exposed.v` | The parameterized relations `V`/`E`/`R`/`G` over a transformation-specific relation `VT` for internal closures; monotonicity; environments of mutually recursive bundles | Fig. 5 |
| `post.v` | λweb versions of CertiRocq's postcondition obligations; `P_ge` (target fuel ≥ source fuel); obligations for removed source / inserted target binding steps and the `Post_dead` families | — |
| `compat.v` | Generic compatibility lemmas (one per form) | §5.1 "Mechanization details" |
| `dead.v` | Compatibility lemmas for binding steps taken by one side only (dead `Econstr`/`Eproj`/`Efun` in the source, inserted constants in the target) | — |
| `select.v` | Transforming a subset of the webs: `VT_sel sel VT` uses `VT` for closures of selected webs and the unchanged calling convention (`V_fun`) for the others | — |
| `bound.v` | `dead_bound L G`, the λweb counterpart of CertiRocq's `inline_bound`: a `Post_dead` family with an upper bound (divergence preservation) | — |
| `indep.v` | Exposed values do not depend on `VT`; top-level relations; any instantiation implies the λweb relation | Thm 5.1, Cor 5.2 |
| `refl.v` | Identity instantiation, fundamental property, reflexivity of the λweb relation | — |
| `dpe.v` | Flow-directed dead-parameter elimination over mutually recursive bundles, also dropping dead local bindings | §6.1, Fig. 6, Thms 5.3/5.4 |
| `dpe_impl.v` | An implementation of DPE (liveness analysis per web, dead-binding elimination) and the proof that it inhabits the relation | — |
| `cp.v` | Flow-directed constant propagation with locally bound constants (and constant parameters), dropping dead local bindings | §6.2, Fig. 7 |
| `cp_impl.v` | An implementation of constant propagation: an iterated analysis, the transformation, and a checker proven sound | — |
| `defunc.v` | MLton-style defunctionalization of lambda-lifted programs: closures of the selected webs become records, calls become a case over the lambda set and a named call of the code function; mixed bundles; join points; correctness and refinement (incl. divergence) | §6.3 |
| `comp.v` | Transitive closure, adequacy and linking for λweb | §7.3, Lemmas 7.5, 7.6 |
| `dfn_impl.v` | An implementation of defunctionalization: wrapper analysis, fresh tags and inductive types for the lambda sets (extending the constructor environment), the transformation, and a checker proven sound | — |
| `erase.v` | Cross-language erasure relation λweb → λANF; `erase` is correct; adequacy; linking | §7.4, Fig. 11, Lemmas 7.7, 7.8 |
| `anno.v` | Cross-language annotation relation λANF → λweb (the spec of an analysis); adequacy; linking | §7.2, Fig. 10, Lemmas 7.3, 7.4 |
| `pipeline.v` | Composition with CertiRocq's `preord_exp_n`: refinement and linking for the whole pipeline; a compiler built from correct phases is correct | §7.5, Lemmas 7.10, 7.11 |
| `passes.v` | The implemented passes as steps of `web_exp_n` (`dpe_web_n`, `cp_web_n`, `dfn_top_web_n`); the λweb optimizer DPE ; CP ; defunc; a compiler through it, correct across the extension of the constructor environment | — |

Main results: `V_exposed_indep`, `E_top_E_web` (indep.v), `E_web_refl`
(refl.v), `E_web_dpe`, `E_web_dpe_dead`, `dpe_refines` (dpe.v), `E_web_cp`,
`cp_refines` (cp.v), `web_exp_n_refines`,
`web_exp_n_preserves_linking` (comp.v), `erase_correct`, `E_erase_refines`,
`E_erase_preserves_linking` (erase.v), `E_anno_refines`,
`E_anno_preserves_linking` (anno.v), `dfn_correct_top`, `dfn_refines` (defunc.v), `dpe_top_refines`, `cp_top_refines`,
`dfn_top_refines` (implementations), `pipeline_refines`,
`pipeline_preserves_linking`, `compile_refines` (pipeline.v),
`trans_top_preserves_fv` (defunc.v), `web_opt_web_n`, `compile_refines`
(passes.v).

`Print Assumptions` on each of them reports only Rocq's primitive types used
by CertiRocq's primitive values.  The implementations compute (e.g. with
`vm_compute`).

## Building

The files are listed in `theories/_CoqProject`, so they build with the rest
of the theories.  To build only this directory and its dependencies:

```
cd theories && coq_makefile -f _CoqProject -o Makefile
make LambdaWeb/pipeline.vo LambdaWeb/dpe.vo
```

## Design notes

* **Internal constructors** are related structurally (same web, tag and
  related components) by the framework; `VT` only describes internal
  closures.  All case studies of the paper relate internal constructors this
  way.
* **Step indexing.** `VT` receives the value relation only below the current
  index; `VTransProps` asks that it be extensional and monotone in it.
* **Exposure flag.** `bstep ex` evaluates with `ex = true` inside exposed
  functions and at top level; all results must then be exposed.
* **Mutual recursion.** A closure `Vfun ρ B f` is exposed iff the web of `f`
  in `B` is; bundles may mix exposed and internal functions.  Closures of a
  bundle are related by Löb induction on the step index (`Vfun_id`,
  `Vfun_dpe`, `V_e_fun_erase`) and then installed with `G_def_funs`.
* **Webs.** A web is `Exposed p` or `Internal p`; erasure maps both to the
  λANF function tag `p` (`web_tag`), which is enough since erasure only needs
  equal webs to give equal tags.  Passes that need fresh webs (the join
  points of defunctionalization) take an `Internal` index above every one in
  the program.
* **Interface.** Exposed functions keep their λANF function tag `t` as web
  `Exposed t`; exposed constructors use a fixed exposed web `w_con`; the
  linking thunk uses `Exposed lft` for the λANF linking tag `lft`.  λweb linking (`link_w`)
  erases syntactically to λANF's `rel_comp.link`.
* **Erasure** relates every λweb value (exposed or not) to its λANF
  counterpart; this is weaker than the paper's Fig. 11 (which only relates
  exposed values) and is what the composition needs.
* **Typeclass arguments.** Lemmas of `exposed.v`/`compat.v` take the
  `VTransProps VT` instance, which does not occur in their statements; when
  `eapply`ing them, pass `cenv VT` explicitly (e.g.
  `eapply (G_set cenv VT_dpe)`) or let `eauto` discharge the instance goal.

## Not ported yet

* Linking for the compiler of `passes.v`: defunctionalization extends the
  constructor environment per compilation unit, so separately compiled units
  would have to agree on the new tags.

## Defunctionalization (`defunc.v`)

The pass runs after lambda lifting.  The source is `Efun Btop e0`, where the
code functions `Btop` are kept unchanged (they may have free variables only if
the program does).  A web `w` is selected when it has a lambda set `L ! w`;
every function of a selected web must be a lambda-lifting wrapper
`f xs = code (xs ++ zs)` of a code function (`TB_sel`), with
`T ! c = (code, wc, |E|, args)` for its tag `c`.

* **Shared environments and siblings.** All the wrappers of a bundle are
  represented by records `C_f(E)` with the same fields `E`, the environment of
  the bundle, which contains no wrapper of the bundle.  The extra arguments
  `zs` of a wrapper are described by `args`: `AEnv i` is the `i`-th field of
  `E`, and `ASib w' c'` is a sibling wrapper, whose record `C_c'(E)` is
  rebuilt from the same fields at the call.  So mutually recursive closures
  (wrappers capturing themselves or their siblings) are defunctionalized
  without cyclic records.  `E` must be free in, or defined by, the bundle.
* A bundle may mix wrappers and other functions: the other functions stay in
  an `Efun` (`fun_recs`), and rebuild the records of their wrapper siblings on
  entry.
* A call through a selected web becomes a case over the lambda set whose
  branches project the fields into fresh variables, rebuild the sibling
  records (`arg_binds`) and call the code function by name; the continuation
  of a bound call is duplicated or put in a join point (`Trans_letapp_join`).
* `VT_dfn` relates a wrapper closure to its record: the code closure in its
  environment is related to the target code function of the tag, and its
  extra arguments to the values rebuilt from the fields (`arg_vals`); for a
  sibling, this is the relation of the sibling's closure and record at a
  lower index, which the Löb induction of `V_bundle` provides.  Unselected internal closures keep their
  calling convention (`select.v`).
* A selected call takes two steps in the source (wrapper, code) and a case,
  the projections and one call in the target: the inner call relation is
  proven with `P_sh` (the target may be one step behind), which the case step
  turns into `P_ge`.

The implementation (`dfn_impl.v`) selects the internal webs whose functions
are all wrappers of code functions, gives every wrapper a fresh tag and
every selected web a fresh inductive type, computes the environment of every
bundle and the arguments of its wrappers, and checks the side conditions;
if the check fails, it returns the program unchanged.  `dfn_top_refines`
relates the source under the original constructor environment to the target
under the extended one.

## Web subsets (`select.v`)

A pass need not transform every internal web.  With `sel w` saying which
webs it transforms, a function or call of web `w` is left unchanged when
`keeps sel w` (it is exposed, or not selected), and is then handled by the
generic compatibility lemmas exactly like an exposed one.  The pass's own
relation `VT` only has to describe closures of selected webs; `VT_sel sel VT`
relates the other internal closures by `V_fun`.  DPE and constant
propagation select the webs that have an entry in their map (`sel_L`), so
known functions, or any web the analysis has no use for, can simply be left
out of the map.

## Dead bindings and constants (`dpe.v`, `cp.v`)

Both relations are indexed by a budget `n`, the number of dead bindings that
may be removed on a path of the expression before the next call
(`trans … n e e'`; `trans_weaken` enlarges it), and by `Gb`, the budget of
function bodies.  A binding `Econstr x …`, `Eproj x …` or `Efun B …` may be
dropped when its variables do not occur in the *transformed* continuation,
so bindings made dead by the transformation itself (an argument that DPE or
constant propagation stopped passing) are removed too.

Removed source steps are accounted for by a family of postconditions
`P : nat -> PostT` (`Post_dead`, post.v): `P n` must satisfy the usual
obligations and absorb one removed step into `P (S n)`, and bodies are
checked against `P Gb ⊆ PG`.  This is the structure of CertiRocq's
`inline_bound L G`.  `dead_bound n Gb` (bound.v), which bounds source fuel by
`target fuel + Gb·calls + n`, is an instance with an upper bound, so
`dpe_refines` and `cp_refines` preserve divergence.  For any single
postcondition, `E_web_dpe` covers DPE without dead bindings (`Gb = n = 0`).

Constant propagation (`cp.v`) tracks a scoped constant environment `K`.
`Econstr x w c [] e` records `x ↦ (c, w)`, also when the binding is dropped,
and other binders of `x` forget it.  A constant parameter of an internal
function is recorded in its body, so recursive calls can pass it on.
`Lc` maps an internal web to its parameters' constants.  Calls drop the
constant arguments, which must be recorded in `K`.  Functions drop the
corresponding parameters (they must be distinct) and rebind them on entry
(`bind_consts`): these are inserted target steps, so `P Gb` must satisfy
`post_target_step`.
