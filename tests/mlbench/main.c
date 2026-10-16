/* Runs the compiled program once and prints its integer result.  With
   CALLS, also prints the known and closure calls it made (see calls.py); with
   ALLOC, the words it allocated (with gc_count.c). */
#include <stdio.h>
#include "gc_stack.h"

extern value body(struct thread_info *);
#ifdef CALLS
unsigned long long ho_k, ho_u;
#endif
#ifdef ALLOC
extern unsigned long long certirocq_alloc_words;
#endif

int main(int argc, char *argv[]) {
  struct thread_info *tinfo = make_tinfo();
  value v = body(tinfo);
  printf("%llu", ((unsigned long long) v) >> 1);
#ifdef CALLS
  printf(" %llu %llu", ho_k, ho_u);
#endif
#ifdef ALLOC
  printf(" %llu", certirocq_alloc_words + (unsigned long long)(tinfo->alloc - tinfo->heap->spaces[0].start));
#endif
  printf("\n");
  return 0;
}
