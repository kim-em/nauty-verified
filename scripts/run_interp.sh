#!/usr/bin/env bash
# Run the Lean interpreter on the pinned Clight of the linked dense and sparse
# programs (nvInterp) on every fixture and compare with the recorded output
# (tests/fixtures/*.out and *.sparse.out).
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
(cd "$root" && lake build nvInterp >/dev/null) || exit 1
err=$(mktemp); trap 'rm -f "$err"' EXIT
fail=0
for g in "$root"/tests/fixtures/*.json; do
  name=$(basename "$g" .json)
  for kind in dense sparse; do
    if [ $kind = dense ]; then rec="$name.out"; else rec="$name.sparse.out"; fi
    out=$(python3 "$root/scripts/graph_input.py" --$kind "$g" | "$root/.lake/build/bin/nvInterp" --$kind 2>"$err")
    if [ "$out" = "$(cat "$root/tests/fixtures/$rec")" ]; then
      echo "ok $kind $name ($(sed -n 's/.*after \([0-9]*\) steps/\1/p' "$err") steps)"
    else
      echo "FAIL $kind $name: $(cat "$err")"; fail=1
    fi
  done
done
exit $fail
