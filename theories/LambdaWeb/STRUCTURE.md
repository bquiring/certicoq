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

There is no flow analysis: the analysis phase is specified by the annotation
relation (`anno.v`) and assumed in `pipeline.v`.

## Files

| File | Contents | Paper |
| :--- | :--- | :--- |
| `syntax.v` | λweb syntax and values, the abstract exposed webs, exposed and well-formed values, erasure to λANF, free variables (inherited through erasure) | Fig. 3, Fig. 4 (top) |
| `semantics.v` | Fuel/trace big-step semantics with web and exposure checks; determinism, fuel lemmas, preservation of well-formedness | Fig. 4, Lemma 4.1 |
| `exposed.v` | The parameterized relations `V`/`E`/`R`/`G` over a transformation-specific relation `VT` for internal closures; monotonicity; environments of mutually recursive bundles | Fig. 5 |
| `post.v` | λweb versions of CertiRocq's postcondition obligations | — |
| `compat.v` | Generic compatibility lemmas (one per form) | §5.1 "Mechanization details" |
| `indep.v` | Exposed values do not depend on `VT`; top-level relations; any instantiation implies the λweb relation | Thm 5.1, Cor 5.2 |
| `refl.v` | Identity instantiation, fundamental property, reflexivity of the λweb relation | — |
| `dpe.v` | Flow-directed dead-parameter elimination over mutually recursive bundles | §6.1, Fig. 6, Thms 5.3/5.4 |
| `comp.v` | Transitive closure, adequacy and linking for λweb | §7.3, Lemmas 7.5, 7.6 |
| `erase.v` | Cross-language erasure relation λweb → λANF; `erase` is correct; adequacy; linking | §7.4, Fig. 11, Lemmas 7.7, 7.8 |
| `anno.v` | Cross-language annotation relation λANF → λweb (the spec of an analysis); adequacy; linking | §7.2, Fig. 10, Lemmas 7.3, 7.4 |
| `pipeline.v` | Composition with CertiRocq's `preord_exp_n`: refinement and linking for the whole pipeline; a compiler built from correct phases is correct | §7.5, Lemmas 7.10, 7.11 |

Main results: `V_exposed_indep`, `E_top_E_web` (indep.v), `E_web_refl`
(refl.v), `E_web_dpe` (dpe.v), `web_exp_n_refines`,
`web_exp_n_preserves_linking` (comp.v), `erase_correct`, `E_erase_refines`,
`E_erase_preserves_linking` (erase.v), `E_anno_refines`,
`E_anno_preserves_linking` (anno.v), `pipeline_refines`,
`pipeline_preserves_linking`, `compile_refines` (pipeline.v).

`Print Assumptions` on each of them reports only `exposedb` (the abstract set
of exposed webs) and Rocq's primitive types used by CertiRocq's primitive
values.

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
* **Interface.** Exposed functions keep their λANF function tag as web;
  exposed constructors use a fixed web `w_con`; the linking thunk uses the
  λANF linking tag `lft`, which must be exposed.  λweb linking (`link_w`)
  erases syntactically to λANF's `rel_comp.link`.
* **Erasure** relates every λweb value (exposed or not) to its λANF
  counterpart; this is weaker than the paper's Fig. 11 (which only relates
  exposed values) and is what the composition needs.
* **Typeclass arguments.** Lemmas of `exposed.v`/`compat.v` take the
  `VTransProps VT` instance, which does not occur in their statements; when
  `eapply`ing them, pass `cenv VT` explicitly (e.g.
  `eapply (G_set cenv VT_dpe)`) or let `eauto` discharge the instance goal.

## Not ported yet

* Constant propagation and defunctionalization (paper §6.2, §6.3).  Both add
  target-only evaluation steps (inserted constructor bindings, case dispatch),
  so under CertiRocq's postconditions they need an extra closure property of
  `PG` for target-side steps; DPE does not.
* A flow analysis inhabiting the annotation relation (the pipeline assumes
  one).
