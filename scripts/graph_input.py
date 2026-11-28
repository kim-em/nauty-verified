"""Write the harness's input stream for a graph given as JSON.

The JSON has `n`, `colors` (length n) and `edges` (pairs), as in hex-dev's
conformance-fixtures/HexGraphIso/*.json. Duplicate and reversed edges are
merged. By default the stream is the dense harness's; with --sparse it is the
sparse harness's: n, the colours, the degrees, then each vertex's neighbours
in increasing order (the sorted rows of HexGraph's SparseGraph)."""
import json
import sys


def stream(graph):
    n = graph["n"]
    edges = sorted({tuple(sorted(e)) for e in graph["edges"]})
    out = [n, *graph["colors"], len(edges)]
    for a, b in edges:
        out += [a, b]
    return out


def sparse_stream(graph):
    n = graph["n"]
    rows = [set() for _ in range(n)]
    for a, b in graph["edges"]:
        if a != b:
            rows[a].add(b)
            rows[b].add(a)
    out = [n, *graph["colors"], *(len(r) for r in rows)]
    for r in rows:
        out += sorted(r)
    return out


if __name__ == "__main__":
    args = sys.argv[1:]
    make = sparse_stream if args[0] == "--sparse" else stream
    print("\n".join(map(str, make(json.load(open(args[-1]))))))
