"""Compare the sparse harness's output (first file) with HexGraphIso's
(second file, from nvSparseExpected).

The canonical labelling, orbits, canonical graph and statistics (tags 2 to 5)
must be equal. The pinned hex-graph-iso writes every admitted automorphism
(`genTrace`), nauty only those that join orbits, so until the re-pin to
`TraceRun.emitted` (docs/PLAN.md, Phase 6) the generators nauty writes
(tag 1) must be a subsequence of HexGraphIso's."""
import sys


def parse(xs, n):
    gens, i = [], 0
    while i < len(xs) and xs[i] == 1:
        gens.append(tuple(xs[i + 1:i + 1 + n]))
        i += 1 + n
    return gens, xs[i:]


def main():
    a = [int(x) for x in open(sys.argv[1]).read().split()]
    b = [int(x) for x in open(sys.argv[2]).read().split()]
    n = int(sys.argv[3])
    ga, ra = parse(a, n)
    gb, rb = parse(b, n)
    if ra != rb:
        print("labelling, orbits, canonical graph or statistics differ")
        return 1
    it = iter(gb)
    if not all(g in it for g in ga):
        print("nauty's generators are not a subsequence of HexGraphIso's")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
