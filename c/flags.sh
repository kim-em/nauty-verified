# The pinned build configuration of nauty, shared by every build of the
# verified program (CompCert4Lean, the exporter, native tests).
#
# WORDSIZE=64            64-bit setwords, as in HexGraphIso's pinned target.
# HAVE_HWLZCNT=0,        nauty's portable table-based FIRSTBITNZ and POPCOUNT
# HAVE_HWPOPCNT=0        instead of compiler builtins outside CompCert's C.
# malloc=nauty_zalloc    every allocation zero-fills (see harness/zalloc.c).
NAUTY_FLAGS="-DWORDSIZE=64 -DHAVE_HWLZCNT=0 -DHAVE_HWPOPCNT=0"
NAUTY_ALLOC_FLAG="-Dmalloc=nauty_zalloc"
# Translation units of the verified dense program. schreier.c and naurng.c
# are linked only to resolve references on code paths the pinned options
# never take.
NAUTY_SOURCES="nauty nautil naugraph schreier naurng"
