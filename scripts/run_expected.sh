#!/usr/bin/env bash
# Compare the recorded sparse harness output on every fixture
# (tests/fixtures/*.sparse.out, which scripts/run_native.sh checks against
# the native build) with HexGraphIso's sparse search evaluated in Lean
# (nvSparseExpected, the numbers `expectedSparse` gives), as
# scripts/compare_sparse.py describes.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
(cd "$root" && lake build nvSparseExpected >/dev/null) || exit 1
hex=$(mktemp); trap 'rm -f "$hex"' EXIT
fail=0
for g in "$root"/tests/fixtures/*.json; do
  name=$(basename "$g" .json)
  python3 "$root/scripts/graph_input.py" --sparse "$g" > "$hex.in"
  "$root/.lake/build/bin/nvSparseExpected" < "$hex.in" > "$hex"
  if python3 "$root/scripts/compare_sparse.py" "$root/tests/fixtures/$name.sparse.out" "$hex" \
      "$(head -1 "$hex.in")"; then
    echo "ok $name"
  else
    echo "FAIL $name"; fail=1
  fi
  rm -f "$hex.in"
done
exit $fail
