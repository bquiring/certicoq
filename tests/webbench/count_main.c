/* Runs the compiled program once and reports the words it allocated. */
#include <stdio.h>
#include "gc_stack.h"

extern value body(struct thread_info *);
extern unsigned long long certirocq_alloc_words;

int main(void) {
  struct thread_info *tinfo = make_tinfo();
  body(tinfo);
  unsigned long long words = certirocq_alloc_words + (unsigned long long)(tinfo->alloc - tinfo->heap->spaces[0].start);
  printf("%llu\n", words);
  return 0;
}
