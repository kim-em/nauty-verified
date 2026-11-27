#!/usr/bin/env bash
# Run the Lean interpreter on the pinned Clight of the linked dense program
# (nvInterp) on every fixture and compare with the recorded output.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
(cd "$root" && lake build nvInterp >/dev/null) || exit 1
fail=0
for g in "$root"/tests/fixtures/*.json; do
  name=$(basename "$g" .json)
  out=$(python3 "$root/scripts/graph_input.py" "$g" | "$root/.lake/build/bin/nvInterp" 2>/tmp/nvinterp.err)
  if [ "$out" = "$(cat "$root/tests/fixtures/$name.out")" ]; then
    echo "ok $name ($(sed -n 's/.*after \([0-9]*\) steps/\1/p' /tmp/nvinterp.err) steps)"
  else
    echo "FAIL $name: $(cat /tmp/nvinterp.err)"; fail=1
  fi
done
exit $fail
