"""Write the dense harness's input stream for a graph given as JSON.

The JSON has `n`, `colors` (length n) and `edges` (pairs), as in hex-dev's
conformance-fixtures/HexGraphIso/*.json. Duplicate and reversed edges are
merged."""
import json
import sys


def stream(graph):
    n = graph["n"]
    edges = sorted({tuple(sorted(e)) for e in graph["edges"]})
    out = [n, *graph["colors"], len(edges)]
    for a, b in edges:
        out += [a, b]
    return out


if __name__ == "__main__":
    print("\n".join(map(str, stream(json.load(open(sys.argv[1]))))))
