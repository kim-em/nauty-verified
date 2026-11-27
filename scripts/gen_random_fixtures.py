"""Generate the seeded random graphs in tests/fixtures (random-*.json).

Orders 1 to 16, edge densities from sparse to dense, one to three colours.
Rerunning reproduces the same files."""
import json
import random
from pathlib import Path

rng = random.Random(20261127)
out = Path(__file__).resolve().parent.parent / "tests" / "fixtures"
for i in range(48):
    n = 1 + i % 16
    p = [0.1, 0.3, 0.5, 0.8][i % 4]
    k = 1 + (i // 16)
    colors = [rng.randrange(k) for _ in range(n)]
    present = sorted(set(colors))
    colors = [present.index(c) for c in colors]
    edges = [[a, b] for a in range(n) for b in range(a + 1, n) if rng.random() < p]
    (out / f"random-{i:02d}.json").write_text(
        json.dumps({"n": n, "k": len(present), "colors": colors, "edges": edges}) + "\n")
