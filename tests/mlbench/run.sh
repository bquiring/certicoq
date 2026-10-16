#!/usr/bin/env bash
# Compares MLton with CertiRocq at -O 1 (base) and -O 2 (web optimizations,
# with defunctionalization) on ports of programs of the 3CPS suite.  Checks
# that every binary prints the same checksum, then reports user-space
# instructions and the median user time of TRIALS runs.
set -eu
CC=${CC:-gcc}
RT=../../runtime
CFLAGS="-O2 -flto -fomit-frame-pointer -w -I. -I$RT"  # -flto inlines the primitives of prim_int63.c
TRIALS=${TRIALS:-5}
mkdir -p build
instr() { taskset -c 0 perf stat -x, -e instructions:u "$@" 2>&1 >/dev/null | awk -F, '$1 ~ /^[0-9]+$/ { s += $1 } END { print s + 0 }'; }
utime() {
  for i in $(seq $TRIALS); do /usr/bin/time -f "%U" taskset -c 0 "$@" 2>&1 >/dev/null | tail -1; done | sort -n | awk '{ a[NR] = $1 } END { print a[int((NR + 1) / 2)] }'
}
printf "%-12s %12s %12s %12s %7s %7s %8s %8s %8s\n" program "instr MLton" "instr -O1" "instr -O2" "O1/ML" "O2/ML" "t MLton" "t -O1" "t -O2"
for p in $(cat PROGS); do
  mlton -default-type int64 -default-type word64 -output build/${p}_mlton sml/$p.sml
  exp=$(./build/${p}_mlton)
  for v in base web; do
    $CC $CFLAGS -o build/${p}_$v main.c $RT/gc_stack.c $RT/prim_int63.c CertiRocq.Tests.mlbench.mlbench.${p}_bench_$v.c
    got=$(ulimit -s unlimited; ./build/${p}_$v)
    if [ "$got" != "$exp" ]; then echo "FAIL ${p}_$v: $got, MLton $exp" >&2; fi
  done
  im=$(instr ./build/${p}_mlton); ib=$(bash -c "ulimit -s unlimited; $(declare -f instr); instr ./build/${p}_base"); iw=$(bash -c "ulimit -s unlimited; $(declare -f instr); instr ./build/${p}_web")
  tm=$(utime ./build/${p}_mlton); tb=$(bash -c "ulimit -s unlimited; TRIALS=$TRIALS; $(declare -f utime); utime ./build/${p}_base"); tw=$(bash -c "ulimit -s unlimited; TRIALS=$TRIALS; $(declare -f utime); utime ./build/${p}_web")
  printf "%-12s %12s %12s %12s %7.2f %7.2f %8s %8s %8s\n" $p $im $ib $iw \
    $(awk -v a=$ib -v b=$im 'BEGIN{print a/b}') $(awk -v a=$iw -v b=$im 'BEGIN{print a/b}') $tm $tb $tw
done
