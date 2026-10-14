/* Runs the compiled program ITERS times and reports the time per run. */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "gc_stack.h"

extern value body(struct thread_info *);

int main(int argc, char *argv[]) {
  long iters = argc > 1 ? atol(argv[1]) : 1;
  struct thread_info *tinfo = make_tinfo();
  struct timespec t0, t1;
  clock_gettime(CLOCK_MONOTONIC, &t0);
  for (long i = 0; i < iters; i++) body(tinfo);
  clock_gettime(CLOCK_MONOTONIC, &t1);
  double s = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) / 1e9;
  printf("%.9f\n", s / iters);
  return 0;
}
