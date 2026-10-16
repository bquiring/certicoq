# λweb in CertiRocq: next steps

State as of 2026-10-16 (branch `lambdaweb`, d941f353). Everything in the
`-O 2` pipeline is proven, with no admits and no axioms beyond the primitive
types and `functional_extensionality_dep`. See `STRUCTURE.md` for the layout.

## 1. Defunctionalization quality

- **Skip the dispatch `case` for single-constructor webs.** When a web has
  one lambda, a defunctionalized call should jump straight to the code
  instead of going through a one-branch `case`. This is the likely cause of
  the small webbench regressions after single-lambda defunc (3be55669):
  vs_hard 0.878 → 0.884 instr and 0.267 → 0.290 alloc, color 0.769 → 0.774
  and 0.640 → 0.666, vs_easy alloc 0.520 → 0.557. This needs a spec change
  in `defunc.v` (a dispatch rule without `Ecase`) and matching cases in
  `dfn_impl.v`.
- **Tail calls.** We saw defunc break a tail call earlier and deferred it.
  Reproduce it on hobench and check whether the dispatcher is called with
  `Eletapp` where the source used `Eapp`.
- **fmap.** Its one remaining closure web is a 0-CFA imprecision:
  `fold_left` is used with closure and int accumulators, so closures reach
  `halt` and become exposed. That needs 1-CFA or polyvariance. The analysis
  side should link fine (any analysis proven against `E_anno_top` links).
- **Heuristics.** The pre-pass that lambda-lifts, eta-expands and picks
  webs is still implicit. Decide what to defunctionalize from size and
  call-site counts instead of "≥ 1 lambda".

## 2. Arity raising and flow precision

- AR flattens almost nothing. Known closure records escape into dispatcher
  environment positions because a web merges all of its call sites. Fixing
  this needs per-call-site flow sets for direct (named) calls, so that a
  known call does not merge with the dispatcher. Running AR before lambda
  lifting finds only 1–2 shaped positions per program.
- Then the field-sensitive AR analysis (`ar_impl.v`, `ar_fix`) should start
  firing. Check it with the `[PASSES]` diagnostics: known positions and
  escape reasons.

## 3. Backend / performance (MLton gap)

The current gap (instructions, CertiRocq -O2 with -flto vs MLton): 1.7–3.5×
on most of tests/mlbench, 8.8× on streams. The front end is no longer the
main cost:
- **Inline the `prim_int63` primitives by default.** Without `-flto` they
  are out-of-line calls; LTO alone gave 1.3–3.6×.
- Shadow-stack spills, thread-info saves around calls, GC and page faults,
  and low IPC. Profile with `perf record -e cycles:u` (it has to launch the
  process).
- The doubling-loop fuel matches account for part of the instruction counts
  in mlbench. Make sure the SML side counts the same work.

## 4. Smaller passes

- **Uncurrying web pass** (low value). CertiRocq's uncurry pass catches most
  cases. The rest are functions returning a lambda after a `match`
  (relabel, mapM, chain, expr). The plan is a wrapper plus an uncurried
  copy, run before lambda lifting. The `stats.curry_of` diagnostics show
  what is left.
- Instruction regressions in webbench's rec_clos and compile.

## 5. Proof loose ends

- Backend consistency between fenv and cenv for the fresh tags that
  `retag.v` adds is checked at runtime (`fenv_of` returns a flag), not
  proven end to end.
- The fast CFA solver (`LambdaCFA/fast.v`) and the fixpoint solver
  (`fixpoint.v`) are proven. The CFA fallback paths (trivial solution,
  freshen precondition) are proven but silently lose optimizations. Log
  when they trigger.

## How to resume

```
eval $(opam env --switch=rocq91 --set-switch)
make -C theories -j4 LambdaCFA/toplevel_correct.vo Extraction/extraction.vo
bash ./make_plugin.sh plugin
cd tests/hobench  && ./rc.sh hobench.v && (ulimit -s unlimited; ./counts.sh)
cd tests/mlbench  && ./rc.sh mlbench.v && ./run.sh
cd tests/webbench && TRIALS=1 TARGET=0.05 bash run.sh && bash counts.sh
```
The only failure under `make -k` is the existing one in
`CodegenWasm/LambdaANF_to_Wasm_utils.v`.
