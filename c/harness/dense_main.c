/* Dense nauty on one coloured graph, read through nv_read and reported
   through nv_write.

   Input:  n, then n colours (each >= 0), then the edge count, then each
           edge as two endpoints.
   Output: for each emitted generator, the tag 1 and the n images, in
           emission order; then the tag 2 and the canonical labelling; the
           tag 3 and the n orbit representatives; the tag 4 and the m*n
           setwords of the canonical graph; the tag 5 and the statistics
           numorbits, numgenerators, numnodes, numbadleaves, maxlevel,
           tctotal, canupdates, errstatus.
   The configuration is the one pinned by HexGraphIso: getcanon, caller
   partition, all other options at their defaults. */
#include "nauty.h"
#include "nv_io.h"

static void emit_generator(int count, int *perm, int *orbits, int numorbits,
                           int stabvertex, int n) {
  int i;
  nv_write(1);
  for (i = 0; i < n; ++i) nv_write(perm[i]);
}

int main(void) {
  static DEFAULTOPTIONS_GRAPH(options);
  static char dummyfile;
  statsblk stats;
  int n, m, i, j, c, maxc, pos, ne;
  int *colour, *lab, *ptn, *orbits;
  graph *g, *canong;

  n = (int)nv_read();
  if (n <= 0) { nv_write(-1); return 0; }
  m = SETWORDSNEEDED(n);
  colour = malloc((size_t)n * sizeof(int));
  lab = malloc((size_t)n * sizeof(int));
  ptn = malloc((size_t)n * sizeof(int));
  orbits = malloc((size_t)n * sizeof(int));
  g = malloc((size_t)m * (size_t)n * sizeof(graph));
  canong = malloc((size_t)m * (size_t)n * sizeof(graph));

  maxc = 0;
  for (i = 0; i < n; ++i) {
    colour[i] = (int)nv_read();
    if (colour[i] > maxc) maxc = colour[i];
  }
  ne = (int)nv_read();
  EMPTYGRAPH(g, m, n);
  for (i = 0; i < ne; ++i) {
    int a = (int)nv_read(), b = (int)nv_read();
    ADDONEEDGE(g, a, b, m);
  }

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

  densenauty(g, lab, ptn, orbits, &options, &stats, m, n, canong);

  nv_write(2);
  for (i = 0; i < n; ++i) nv_write(lab[i]);
  nv_write(3);
  for (i = 0; i < n; ++i) nv_write(orbits[i]);
  nv_write(4);
  for (i = 0; i < m * n; ++i) nv_write((long)canong[i]);
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
