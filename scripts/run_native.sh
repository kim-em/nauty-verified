#!/bin/sh
# Build the dense and the sparse harness with the host C compiler and compare
# their output on every tests/fixtures/*.json with the recorded
# tests/fixtures/*.out (dense) and tests/fixtures/*.sparse.out (sparse).
# With --record, write the recorded files instead.
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
. "$root/c/flags.sh"
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
cc=${CC:-cc}
build() {  # name main sources...
  name=$1; shift
  mkdir -p "$work/$name"
  for f in "$@"; do
    src="$root/c/nauty-2.9.3/$f.c"; [ -f "$src" ] || src="$root/c/harness/$f.c"
    $cc -O2 -w $NAUTY_FLAGS $NAUTY_ALLOC_FLAG -I "$root/c/nauty-2.9.3" -I "$root/c/harness" -c "$src" -o "$work/$name/$f.o"
  done
  $cc -o "$work/$name/$name" "$work/$name"/*.o "$work/zalloc.o" "$work/io_stdio.o"
}
$cc -O2 -w -c "$root/c/harness/zalloc.c" -o "$work/zalloc.o"
$cc -O2 -w -I "$root/c/harness" -c "$root/c/harness/io_stdio.c" -o "$work/io_stdio.o"
# shellcheck disable=SC2086
build dense $NAUTY_SOURCES dense_main
# shellcheck disable=SC2086
build sparse $NAUTY_SPARSE_SOURCES sparse_main
status=0
for g in "$root"/tests/fixtures/*.json; do
  name=$(basename "$g" .json)
  for kind in dense sparse; do
    if [ $kind = dense ]; then flag=--dense; rec="$name.out"; else flag=--sparse; rec="$name.sparse.out"; fi
    python3 "$root/scripts/graph_input.py" $flag "$g" | "$work/$kind/$kind" > "$work/$rec"
    if [ "${1:-}" = --record ]; then
      cp "$work/$rec" "$root/tests/fixtures/$rec"
    elif cmp -s "$work/$rec" "$root/tests/fixtures/$rec"; then
      echo "ok   $kind $name"
    else
      echo "FAIL $kind $name"; status=1
    fi
  done
done
exit $status
