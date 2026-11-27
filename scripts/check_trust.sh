#!/bin/sh
# Fail on `axiom` or `native_decide` in our Lean sources, and on any `sorry`
# outside the files listed in scripts/sorry-allowlist.txt.
set -eu
root=$(cd "$(dirname "$0")/.." && pwd); cd "$root"
status=0
if grep -rnE '^\s*(private |protected )?axiom\b|native_decide' NautyVerified NautyVerified.lean; then
  echo "error: axiom or native_decide found"; status=1
fi
for f in $(grep -rlw sorry NautyVerified NautyVerified.lean || true); do
  if ! grep -qxF "$f" scripts/sorry-allowlist.txt; then
    echo "error: sorry in $f, which is not in scripts/sorry-allowlist.txt"; status=1
  fi
done
exit $status
