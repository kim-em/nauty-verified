#!/usr/bin/env bash
# Regenerate c/csyntax/<unit>.json: the CompCert frontend's Csyntax for each
# translation unit, in CompCert4Lean's interchange format.
#
# Usage: scripts/export_csyntax.sh COMPCERT4LEAN_CHECKOUT COMPCERT_CHECKOUT
# The CompCert4Lean checkout must be at the revision in lake-manifest.json;
# the CompCert checkout is the prepared one its compile_c.py expects.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
c4l=$1; compcert=$2
. "$here/c/flags.sh"
out="$here/c/csyntax"; mkdir -p "$out"
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
export_unit() {  # name source extra-flags...
  local name=$1 src=$2; shift 2
  local log="$work/$name.log"
  (cd "$c4l" && python3 scripts/compile_c.py --keep-temps --compcert-root "$compcert" \
     "$@" -I "$here/c/nauty-2.9.3" -I "$here/c/harness" -c "$src" -o "$work/$name.o") > "$log" 2>&1 \
     || { cat "$log"; exit 1; }
  local dir; dir=$(sed -n 's/^Artifacts: //p' "$log" | tail -1)
  python3 -c 'import json,sys; d=json.load(open(sys.argv[1])); json.dump(d, open(sys.argv[2],"w"), separators=(",",":"), sort_keys=True); open(sys.argv[2],"a").write("\n")' \
    "$dir/csyntax.json" "$out/$name.json"
  rm -rf "$dir"
  echo "exported $name"
}
# The units of the dense and the sparse program, each once.
units=$(printf '%s\n' $NAUTY_SOURCES $NAUTY_SPARSE_SOURCES | awk '!seen[$0]++')
for f in $units; do
  # shellcheck disable=SC2086
  export_unit "$f" "$here/c/nauty-2.9.3/$f.c" $NAUTY_FLAGS $NAUTY_ALLOC_FLAG
done
for f in dense_main sparse_main; do
  # shellcheck disable=SC2086
  export_unit "$f" "$here/c/harness/$f.c" $NAUTY_FLAGS $NAUTY_ALLOC_FLAG
done
export_unit zalloc "$here/c/harness/zalloc.c"
