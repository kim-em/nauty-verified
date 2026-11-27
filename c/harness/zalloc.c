/* Zero-filling allocator, used for every allocation in nauty and the
   harness (they are compiled with -Dmalloc=nauty_zalloc; this file is not).

   nauty copies firstcode[0], which it never writes (nauty.c:884). With plain
   malloc that is a read of an undefined value, which CompCert's semantics
   treats as undefined behaviour. Zero-filling makes the value 0. */
#include <stdlib.h>

void *nauty_zalloc(size_t sz) {
  unsigned char *p = malloc(sz);
  size_t i;
  if (p) for (i = 0; i < sz; ++i) p[i] = 0;
  return p;
}
