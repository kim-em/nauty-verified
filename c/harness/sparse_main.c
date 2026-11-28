/* Sparse nauty on one coloured graph, read through nv_read and reported
   through nv_write.

   Input:  n, then n colours (each >= 0), then the n degrees, then the
           neighbours of each vertex in turn (vertex 0's first), each list
           in the order the graph stores it.
   Output: for each emitted generator, the tag 1 and the n images, in
           emission order; then the tag 2 and the canonical labelling; the
           tag 3 and the n orbit representatives; the tag 4 and, for each
           vertex of the canonical graph in turn, its degree followed by its
           neighbours in the order sparsenauty stored them; the tag 5 and the
           statistics numorbits, numgenerators, numnodes, numbadleaves,
           maxlevel, tctotal, canupdates, errstatus.
   The configuration is the one pinned by HexGraphIso: getcanon, caller
   partition, all other options at their defaults. The offsets given to
   nauty are the running sums of the degrees, and the edge array always has
   at least one entry, so it is never NULL. */
#include "nausparse.h"
#include "nv_io.h"

static void emit_generator(int count, int *perm, int *orbits, int numorbits,
                           int stabvertex, int n) {
  int i;
  nv_write(1);
  for (i = 0; i < n; ++i) nv_write(perm[i]);
}

int main(void) {
  static DEFAULTOPTIONS_SPARSEGRAPH(options);
  static char dummyfile;
  statsblk stats;
  sparsegraph sg, canong;
  int n, i, j, c, maxc, pos;
  size_t nde, k;
  int *colour, *lab, *ptn, *orbits;

  n = (int)nv_read();
  if (n <= 0) { nv_write(-1); return 0; }
  colour = malloc((size_t)n * sizeof(int));
  lab = malloc((size_t)n * sizeof(int));
  ptn = malloc((size_t)n * sizeof(int));
  orbits = malloc((size_t)n * sizeof(int));

  maxc = 0;
  for (i = 0; i < n; ++i) {
    colour[i] = (int)nv_read();
    if (colour[i] > maxc) maxc = colour[i];
  }

  SG_INIT(sg);
  SG_INIT(canong);
  sg.nv = n;
  sg.v = malloc((size_t)n * sizeof(size_t));
  sg.d = malloc((size_t)n * sizeof(int));
  nde = 0;
  for (i = 0; i < n; ++i) {
    sg.d[i] = (int)nv_read();
    sg.v[i] = nde;
    nde += (size_t)sg.d[i];
  }
  sg.nde = nde;
  sg.e = malloc((nde > 0 ? nde : 1) * sizeof(int));
  for (k = 0; k < nde; ++k) sg.e[k] = (int)nv_read();

  /* Cells in increasing colour order, vertices increasing within a cell. */
  pos = 0;
  for (c = 0; c <= maxc; ++c)
    for (j = 0; j < n; ++j)
      if (colour[j] == c) { lab[pos] = j; ptn[pos] = 1; ++pos; }
  for (i = 0; i < n; ++i)
    if (i == n - 1 || colour[lab[i]] != colour[lab[i + 1]]) ptn[i] = 0;

  options.getcanon = TRUE;
  options.defaultptn = FALSE;
  options.userautomproc = emit_generator;
  options.outfile = (FILE *)&dummyfile;  /* never written: writeautoms is off */

  sparsenauty(&sg, lab, ptn, orbits, &options, &stats, &canong);

  nv_write(2);
  for (i = 0; i < n; ++i) nv_write(lab[i]);
  nv_write(3);
  for (i = 0; i < n; ++i) nv_write(orbits[i]);
  nv_write(4);
  for (i = 0; i < n; ++i) {
    nv_write(canong.d[i]);
    for (j = 0; j < canong.d[i]; ++j) nv_write(canong.e[canong.v[i] + (size_t)j]);
  }
  nv_write(5);
  nv_write(stats.numorbits);
  nv_write(stats.numgenerators);
  nv_write((long)stats.numnodes);
  nv_write((long)stats.numbadleaves);
  nv_write(stats.maxlevel);
  nv_write((long)stats.tctotal);
  nv_write((long)stats.canupdates);
  nv_write(stats.errstatus);
  return 0;
}
