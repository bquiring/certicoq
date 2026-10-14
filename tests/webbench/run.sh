#!/usr/bin/env bash
# Compares the baseline pipeline (-O 1) with the web optimizations (-O 2).
# For each program and variant: check the output against the expected one,
# then time the program body (median of TRIALS trials, each looping the body
# enough times to take about TARGET seconds).

set -eu

CC=${CC:-gcc}
INCLUDE=../../runtime
CFLAGS="-O2 -fomit-frame-pointer -w -I. -I$INCLUDE"
TRIALS=${TRIALS:-5}
TARGET=${TARGET:-0.5}
MOD=${MOD:-bench}
LIST=${LIST:-PROGS}
mkdir -p build

printf "%-10s %14s %14s %8s\n" program "base (s/run)" "web (s/run)" speedup
for p in $(cat $LIST); do
  declare -A t
  for v in base web; do
    c=CertiRocq.Tests.webbench.${MOD}.${p}_${v}.c
    $CC $CFLAGS -o build/${p}_${v}_check ../programs/${p}_main.c glue_${p}.c $INCLUDE/gc_stack.c $c
    if ! ./build/${p}_${v}_check 1 | cmp -s - ../programs/expected_outputs/${p}.txt; then
      echo "FAIL ${p}_${v}: output differs from expected" >&2; exit 1
    fi
    $CC $CFLAGS -o build/${p}_${v}_bench bench_main.c $INCLUDE/gc_stack.c $c
    one=$(./build/${p}_${v}_bench 1)
    iters=$(awk -v o="$one" -v t="$TARGET" 'BEGIN { n = (o > 0) ? int(t / o) : 1000000; if (n < 1) n = 1; print n }')
    runs=()
    for i in $(seq 1 $TRIALS); do runs+=($(./build/${p}_${v}_bench $iters)); done
    t[$v]=$(printf "%s\n" "${runs[@]}" | sort -g | awk '{a[NR]=$1} END {print a[int((NR+1)/2)]}')
  done
  printf "%-10s %14.3e %14.3e %8.3f\n" $p ${t[base]} ${t[web]} $(awk -v b=${t[base]} -v w=${t[web]} 'BEGIN { print b / w }')
  unset t
done
