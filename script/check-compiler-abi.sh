#!/usr/bin/env bash
# Checks that the toolchain in directory NEW can be used with `.olean` files and native code built by
# the toolchain in directory REF (the upstream release this branch identifies as):
# * the compiler-relevant `.olean` data of NEW extends that of REF (see `CompilerABI.lean`), up to the
#   declarations in `compiler-abi-allowlist.txt`;
# * the shared libraries of NEW export all dynamic symbols of those of REF.
#
# usage: script/check-compiler-abi.sh REF NEW
set -euo pipefail
export LC_ALL=C  # for `sort` and `comm`

if [ $# -ne 2 ]; then
  echo "usage: $0 REF NEW" >&2
  exit 2
fi
REF=$(cd "$1" && pwd)
NEW=$(cd "$2" && pwd)
HERE=$(cd "$(dirname "$0")" && pwd)
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

# compile the checker, the interpreter is too slow for comparing every declaration
"$NEW/bin/lean" -c "$TMP/CompilerABI.c" "$HERE/CompilerABI.lean"
"$NEW/bin/leanc" -O2 -o "$TMP/compilerABI" "$TMP/CompilerABI.c"

status=0
"$TMP/compilerABI" check "$REF/lib/lean" "$NEW/lib/lean" "$HERE/compiler-abi-allowlist.txt" \
  'Init.*' 'Std.*' 'Lean.*' 'Lake.*' || status=1

# native code of downstream packages (e.g., precompiled modules) links against the symbols of Lean
# declarations and of the runtime; bundled third-party libraries (GMP, libunwind, libc++) depend on
# how the toolchain was linked
case "$(uname -s)" in
  Linux) ext=so; nm_defined() { nm -D --defined-only "$1" | awk '{ print $NF }' | grep -E '^(l_|lean_|initialize_)' || true; } ;;
  Darwin) ext=dylib; nm_defined() { nm -gU "$1" | awk '{ print $NF }' | grep -E '^_(l_|lean_|initialize_)' || true; } ;;
  *) echo "shared library check not supported on this platform"; exit $status ;;
esac
for lib in "$REF"/lib/lean/*."$ext"; do
  name=$(basename "$lib")
  if [ ! -f "$NEW/lib/lean/$name" ]; then
    echo "error: missing shared library $name"
    status=1
    continue
  fi
  nm_defined "$lib" | sort -u > "$TMP/ref.syms"
  nm_defined "$NEW/lib/lean/$name" | sort -u > "$TMP/new.syms"
  missing=$(comm -23 "$TMP/ref.syms" "$TMP/new.syms" | wc -l)
  echo "$name: $(wc -l < "$TMP/ref.syms") symbols, $missing missing"
  if [ "$missing" -ne 0 ]; then
    comm -23 "$TMP/ref.syms" "$TMP/new.syms" | head -100 | sed 's/^/  missing: /'
    status=1
  fi
done
exit $status
