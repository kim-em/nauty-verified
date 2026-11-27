/* nv_read and nv_write over standard input and output, for native test
   builds. Not part of the verified program. */
#include <stdio.h>
#include <stdlib.h>
#include "nv_io.h"

long nv_read(void) {
  long x;
  if (scanf("%ld", &x) != 1) { fprintf(stderr, "nv_read: end of input\n"); exit(2); }
  return x;
}

void nv_write(long x) { printf("%ld\n", x); }
