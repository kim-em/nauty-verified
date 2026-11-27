#!/usr/bin/env bash
# Build the dense harness binary the end-to-end theorem is about: the linked
# program `NautyVerified.Source.dense.program`, compiled as one program by
# CompCert4Lean (`nvCompile`), expanded and printed by the CompCert4Lean
# bridge, then assembled and linked with the I/O functions and CompCert's
# runtime library. With --check, run it on every fixture.
#
# Usage: scripts/build_binary.sh COMPCERT4LEAN_CHECKOUT COMPCERT_CHECKOUT OUT_DIR [--check]
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
c4l=$1; compcert=$2; out=$3; check=${4:-}
mkdir -p "$out"; out=$(cd "$out" && pwd)
(cd "$here" && lake build nvCompile && .lake/build/bin/nvCompile "$out")
python3 - "$out" "$compcert" <<'PY'
import json, sys
out, compcert = sys.argv[1], sys.argv[2]
json.dump({"operation": "print_named", "root": compcert,
           "configuration": {"pic": False, "pie": False, "common": False, "optimization": "O0"},
           "names": json.load(open(f"{out}/names.json")),
           "input": f"{out}/asm.json", "output": f"{out}/dense.s"}, open(f"{out}/print.json", "w"))
PY
bridge="$c4l/.lake/prototype/bridge/bridge"
[ -x "$bridge" ] || { echo "no bridge at $bridge: run scripts/export_csyntax.sh first" >&2; exit 1; }
COMPCERT_CONFIG="$compcert/compcert.ini" "$bridge" < "$out/print.json" | grep -q '"ok":true'
cc=${CC:-cc}
$cc -c "$out/dense.s" -o "$out/dense.o"
$cc -O2 -w -I "$here/c/harness" -c "$here/c/harness/io_stdio.c" -o "$out/io_stdio.o"
$cc -no-pie -o "$out/dense" "$out/dense.o" "$out/io_stdio.o" "$compcert/runtime/libcompcert.a"
echo "built $out/dense"
if [ "$check" = --check ]; then
  fail=0
  for g in "$here"/tests/fixtures/*.json; do
    name=$(basename "$g" .json)
    if python3 "$here/scripts/graph_input.py" "$g" | "$out/dense" | cmp -s - "$here/tests/fixtures/$name.out"; then
      echo "ok $name"
    else
      echo "FAIL $name"; fail=1
    fi
  done
  exit $fail
fi
