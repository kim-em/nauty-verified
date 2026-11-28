#!/usr/bin/env bash
# Build a harness binary an end-to-end theorem is about: the linked program
# `NautyVerified.Source.dense.program` (or with --sparse
# `NautyVerified.Source.sparse.program`), compiled as one program by
# CompCert4Lean (`nvCompile`), expanded and printed by the CompCert4Lean
# bridge, then assembled and linked with the I/O functions and CompCert's
# runtime library. With --check, run it on every fixture.
#
# Usage: scripts/build_binary.sh COMPCERT4LEAN_CHECKOUT COMPCERT_CHECKOUT OUT_DIR [--sparse] [--check]
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
c4l=$1; compcert=$2; out=$3; shift 3
kind=dense; check=
for a in "$@"; do
  case $a in
    --sparse) kind=sparse ;;
    --check) check=--check ;;
    *) echo "unknown option $a" >&2; exit 2 ;;
  esac
done
mkdir -p "$out"; out=$(cd "$out" && pwd)
(cd "$here" && lake build nvCompile && .lake/build/bin/nvCompile $([ $kind = sparse ] && echo --sparse) "$out")
python3 - "$out" "$compcert" "$kind" <<'PY'
import json, sys
out, compcert, kind = sys.argv[1], sys.argv[2], sys.argv[3]
json.dump({"operation": "print_named", "root": compcert,
           "configuration": {"pic": False, "pie": False, "common": False, "optimization": "O0"},
           "names": json.load(open(f"{out}/names.json")),
           "input": f"{out}/asm.json", "output": f"{out}/{kind}.s"}, open(f"{out}/print.json", "w"))
PY
bridge="$c4l/.lake/prototype/bridge/bridge"
[ -x "$bridge" ] || { echo "no bridge at $bridge: run scripts/export_csyntax.sh first" >&2; exit 1; }
COMPCERT_CONFIG="$compcert/compcert.ini" "$bridge" < "$out/print.json" | grep -q '"ok":true'
cc=${CC:-cc}
$cc -c "$out/$kind.s" -o "$out/$kind.o"
$cc -O2 -w -I "$here/c/harness" -c "$here/c/harness/io_stdio.c" -o "$out/io_stdio.o"
$cc -no-pie -o "$out/$kind" "$out/$kind.o" "$out/io_stdio.o" "$compcert/runtime/libcompcert.a"
echo "built $out/$kind"
if [ "$check" = --check ]; then
  fail=0
  for g in "$here"/tests/fixtures/*.json; do
    name=$(basename "$g" .json)
    rec="$name.out"; [ $kind = sparse ] && rec="$name.sparse.out"
    if python3 "$here/scripts/graph_input.py" --$kind "$g" | "$out/$kind" | cmp -s - "$here/tests/fixtures/$rec"; then
      echo "ok $name"
    else
      echo "FAIL $name"; fail=1
    fi
  done
  exit $fail
fi
