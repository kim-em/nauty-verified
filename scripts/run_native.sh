#!/bin/sh
# Build the dense harness with the host C compiler and compare its output
# on every tests/fixtures/*.json with the recorded tests/fixtures/*.out.
# With --record, write the .out files instead.
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
. "$root/c/flags.sh"
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
cc=${CC:-cc}
for f in $NAUTY_SOURCES dense_main; do
  src="$root/c/nauty-2.9.3/$f.c"; [ -f "$src" ] || src="$root/c/harness/$f.c"
  $cc -O2 -w $NAUTY_FLAGS $NAUTY_ALLOC_FLAG -I "$root/c/nauty-2.9.3" -I "$root/c/harness" -c "$src" -o "$work/$f.o"
done
$cc -O2 -w -c "$root/c/harness/zalloc.c" -o "$work/zalloc.o"
$cc -O2 -w -I "$root/c/harness" -c "$root/c/harness/io_stdio.c" -o "$work/io_stdio.o"
$cc -o "$work/dense" "$work"/*.o
status=0
for g in "$root"/tests/fixtures/*.json; do
  name=$(basename "$g" .json)
  python3 "$root/scripts/graph_input.py" "$g" | "$work/dense" > "$work/$name.out"
  if [ "${1:-}" = --record ]; then
    cp "$work/$name.out" "$root/tests/fixtures/$name.out"
  elif cmp -s "$work/$name.out" "$root/tests/fixtures/$name.out"; then
    echo "ok   $name"
  else
    echo "FAIL $name"; status=1
  fi
done
exit $status
