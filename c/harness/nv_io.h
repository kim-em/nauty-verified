/* Input and output of the verified harness.

   Both are external functions. In CompCert semantics each call is an
   observable event recording its argument or result, so the whole-program
   theorem is a statement about these events. Native test builds link
   io_stdio.c, which implements them over standard input and output. */
#ifndef NV_IO_H
#define NV_IO_H
long nv_read(void);
void nv_write(long x);
#endif
