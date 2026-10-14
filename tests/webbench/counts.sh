#!/usr/bin/env bash
# Instruction counts (user-level, perf) and allocated words (instrumented
# copy of the runtime) of one run of each program, at -O 1 and -O 2.
set -eu
CC=${CC:-gcc}
INCLUDE=../../runtime
CFLAGS="-O2 -fomit-frame-pointer -w -I. -I$INCLUDE"
MOD=${MOD:-bench}
LIST=${LIST:-PROGS}
mkdir -p build
# pinned to one (performance) core, so a single counter counts every instruction
instr() { taskset -c 0 perf stat -x, -e instructions:u "$@" 2>&1 >/dev/null | awk -F, '$1 ~ /^[0-9]+$/ { s += $1 } END { print s + 0 }'; }
# the instructions of the body: one run minus the startup (zero runs)
body_instr() { echo $(( $(instr "$1" 1) - $(instr "$1" 0) )); }
printf "%-10s %14s %14s %7s %14s %14s %7s\n" program "instr -O1" "instr -O2" ratio "alloc -O1" "alloc -O2" ratio
for p in $(cat $LIST); do
  declare -A ins al
  for v in base web; do
    c=CertiRocq.Tests.webbench.${MOD}.${p}_${v}.c
    $CC $CFLAGS -o build/${p}_${v}_count count_main.c gc_count.c $c
    $CC $CFLAGS -o build/${p}_${v}_once bench_main.c $INCLUDE/gc_stack.c $c
    al[$v]=$(./build/${p}_${v}_count)
    ins[$v]=$(body_instr ./build/${p}_${v}_once)
  done
  printf "%-10s %14s %14s %7.3f %14s %14s %7.3f\n" $p ${ins[base]} ${ins[web]} \
    $(awk -v a=${ins[web]} -v b=${ins[base]} 'BEGIN { print a / b }') ${al[base]} ${al[web]} \
    $(awk -v a=${al[web]} -v b=${al[base]} 'BEGIN { print (b > 0) ? a / b : 1 }')
  unset ins al
done
