#!/usr/bin/env bash
# For each program at -O 1 (base) and -O 2 (web): check the result against
# expected.txt, and report the closure calls, instructions and allocated words
# of one run.
set -eu
CC=${CC:-gcc}
RT=../../runtime
CFLAGS="-O2 -fomit-frame-pointer -w -I. -I$RT"
mkdir -p build
instr() { taskset -c 0 perf stat -x, -e instructions:u "$@" 2>&1 >/dev/null | awk -F, '$1 ~ /^[0-9]+$/ { s += $1 } END { print s + 0 }'; }
printf "%-14s %9s %10s %10s %6s %13s %13s %6s %11s %11s %6s\n" program "calls" "clos -O1" "clos -O2" ratio "instr -O1" "instr -O2" ratio "alloc -O1" "alloc -O2" ratio
for p in $(cat PROGS); do
  declare -A clos calls ins al
  exp=$(awk -v p=$p '$1 == p { print $2 }' expected.txt)
  for v in base web; do
    c=CertiRocq.Tests.hobench.hobench.${p}_${v}.c
    python3 calls.py $c build/${p}_${v}_calls.c
    $CC $CFLAGS -DCALLS -o build/${p}_${v}_calls main.c $RT/gc_stack.c $RT/prim_int63.c build/${p}_${v}_calls.c
    $CC $CFLAGS -DALLOC -o build/${p}_${v}_alloc main.c ../webbench/gc_count.c $RT/prim_int63.c $c
    $CC $CFLAGS -o build/${p}_${v} main.c $RT/gc_stack.c $RT/prim_int63.c $c
    read r k u < <(./build/${p}_${v}_calls)
    if [ "$r" != "$exp" ]; then echo "FAIL ${p}_${v}: $r, expected $exp" >&2; exit 1; fi
    calls[$v]=$((k + u)); clos[$v]=$u
    read r a < <(./build/${p}_${v}_alloc); al[$v]=$a
    ins[$v]=$(instr ./build/${p}_${v})
  done
  ratio() { awk -v a=$1 -v b=$2 'BEGIN { print (b > 0) ? a / b : 1 }'; }
  printf "%-14s %9s %10s %10s %6.3f %13s %13s %6.3f %11s %11s %6.3f\n" $p ${calls[base]} ${clos[base]} ${clos[web]} \
    $(ratio ${clos[web]} ${clos[base]}) ${ins[base]} ${ins[web]} $(ratio ${ins[web]} ${ins[base]}) \
    ${al[base]} ${al[web]} $(ratio ${al[web]} ${al[base]})
  unset clos calls ins al
done
