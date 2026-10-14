# LambdaCFA: a compositional 0-CFA for λweb

This directory implements the analysis phase of the λweb pipeline
(`LambdaWeb/anno.v`, `LambdaWeb/passes.v`).  It is a flow-insensitive,
context-insensitive control-flow analysis in the style of 0-CFA that annotates
a λANF program with webs.  The analysis is compositional: the program may be
open, and it is linked against unknown code.

## Files

| File | Contents |
| :--- | :--- |
| `spec.v` | Labels, abstract values (sets of labels, possibly infinite), solutions, and the constraints `ok`/`ok_top` that relate a λANF program to its annotation |
| `sound.v` | The step-indexed cross-language relation indexed by abstract values; import/export with the interface relation `V_a`; the fundamental property; `ok_top_E_anno`: the constraints imply `E_anno_top`; the postcondition `P_eq` (equal fuel) and its obligations |
| `impl.v` | The annotation of a solution (`anno`), a checker proven sound (`check_spec`), the trivial solution (`triv_top`), the solver, and `annotate` with `annotate_correct` |
| `impl_complete.v` | The solver always finishes (`solve_some`, `merge_done`) and its solution always passes the check (`check_solve`), so the fallback is never taken (`analyze_solve`) |
| `fast.v` | The solver used by the compiler: a worklist solver that propagates changes along dependencies, and union-find for webs; its solution is checked as before (`annotate_fast_correct`) |
| `compile.v` | The compiler of `LambdaWeb/passes.v` with this analysis (`compile_cfa_refines`, assuming only the λANF optimizations); linking of separately annotated units (`annotate_preserves_linking`), including with units annotated by any other analysis proven against `E_anno_top` (`annotate_links_with_lib`, `annotate_links_with_client`) |

Main results: `ok_top_E_anno` (sound.v), `annotate_correct` (impl.v),
`compile_cfa_refines` and `annotate_preserves_linking` (compile.v).
`Print Assumptions` on each reports only Rocq's primitive types.

## The analysis

Abstract values are sets of labels:

* `ltop`: a value of the unknown context;
* `lfun f`: a closure of a function named `f`;
* `lcon x`: a constructor allocated at a binding of `x`.

A solution gives a flow set to every variable and, to each label, abstract
arguments and results (functions) or fields (constructors).  It also gives the
set of exposed labels and an internal web for each internal label.  Sets may
be infinite (`AAll`), so the trivial solution, where everything flows
everywhere and is exposed, is a solution.  Binding names need not be unique:
constraints are generated for every binding occurrence, so a name bound twice
merges its flows.

The constraints (`ok`):

* **Use sites.** Every call, projection and case analysis has a web shared by
  the labels of the right kind in the flow set of its subject.  If `ltop` is
  in the set, the web is exposed: `Exposed t` for a call with λANF tag `t`,
  `w_con` for a constructor use.
* **Exposed labels.** Exposed functions have web `Exposed t` for their λANF
  tag; their arguments come from the context and their results escape.
  Exposed constructors have web `w_con` and their fields escape.
* **Escape.** The arguments of exposed calls escape (every label in the set
  is exposed), as does the result of the program.  The free variables of the
  program and the results of unknown functions come from the context.
* **Flows.** Arguments flow to parameters through the abstract arguments of
  the callee labels, and results flow back.  Fields flow into constructors and
  out of projections.

## The proof

`V k A v1 v2` relates a λANF value to its annotation when one of the
following holds:

* `ltop ∈ A` and the values are related by the interface relation `V_a` of
  `anno.v` (a value of the context);
* `v1` is a constructor of a label in `A`, annotated with the label's web,
  with fields related at the abstract fields;
* `v1` is a closure of a label in `A`, annotated with the label's web, whose
  body is related when called on arguments related at the abstract
  arguments, with the result related at the abstract result.

`V_import` turns `V_a` into `V` at any set containing `ltop`.  `V_export` turns
`V` at an escaping set into `V_a`.  Their proof is a mutual induction on the
step index and the value: an exposed closure is exported by importing its
arguments and exporting its result.  The fundamental property is by induction
on the step index and the constraints, with Löb induction for the closures of
a bundle (`V_clo`) and a shared lemma for calls (`call_rel`).  The annotation
does not change the steps of the program, so both programs use the same fuel
(`P_eq`).

## Compositionality

The 0-CFA's relation `V` (indexed by abstract sets) is internal to
`sound.v`.  At the boundary of a unit it is converted to the
analysis-independent interface relation `V_a` (`V_import`, `V_export`), so
the result `E_anno_top` mentions nothing about the analysis.  A unit annotated
by this analysis therefore links with a unit annotated by any other analysis,
such as a k-CFA, proven against `E_anno_top` at the same interface: exposed
constructors at `w_con`, exposed functions at `Exposed t`, and the same
postconditions (`P_eq`).  Internal webs never cross the boundary, so the two
analyses need not coordinate their internal web names.

## The implementation

The solver (`impl.v`) iterates a pass over the program until the
state stops growing.  The pass propagates flows, arguments and results,
exposure and escape.  It then merges the internal webs of labels that share a
use site.  A label's internal web is `Internal p` for the smallest label index
`p` in its class.

Both loops run on binary fuel (`loop`), which is enough to always finish
(`impl_complete.v`):

* Every operation of a pass only adds to the state.  The state is measured
  within the universe of the program (its variables, their labels, and the
  largest arity), and that measure is bounded by `ubound`, roughly
  variables² × arity.  The fuel is one more than the bound, so a pass that
  changes nothing is always reached (`solve_some`).  A fuel linear in the
  program is not enough: a value that only enters a chain of n functions
  after the previous value has gone through it takes n rounds per value.
* Each merging pass only lowers webs, so the sum of the webs bounds the
  passes (`merge_done`).

`check` decides `ok_top` for the annotation of the solution (`check_spec`).
When the check fails, `annotate` falls back
to the trivial solution, which annotates every value as exposed (`triv_top`).
So `annotate` is correct for every program.

`impl_complete.v` proves that the fallback is never taken
(`analyze_solve`):

1. Every operation of the solver stays within the universe of the program
   (`inv`, `round_inv`), so when the measure stops growing the state is a
   true fixpoint of a round (`fix_le`, `solve_loop_fix`).
2. Every operation of a round only adds to the state, so in a round that
   adds nothing, everything each operation would add is already there.  This
   gives the flow constraints (`step_C`), the escape of the result, the rules
   for exposed labels and the free variables (`solve_loop_C`).
3. Merging stops at a pass that changes nothing, so the internal labels of a
   use site share a web (`merge_fix`).
4. From these, the checker accepts the solution (`check_solve`).

The checker is still what `annotate_correct` relies on, so the solver is
proven complete rather than trusted.

## Limitations

* The analysis is 0-CFA: one abstract value per variable, with no context or
  flow sensitivity.  Projections and case analyses do not filter by
  constructor tag.
* Internal function webs erase to fresh λANF function tags (the index of the
  web, the encoded label).  The pipeline's correctness does not depend on
  them, but a backend that looks function tags up in a function environment
  would need entries for them.
