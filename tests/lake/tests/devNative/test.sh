#!/usr/bin/env bash
source ../common.sh

./clean.sh

# ---
# Tests that with `LEAN_DEV_NATIVE=1`, the development toolchain's Lake compiles the dependency
# modules imported by the root package into cached native libraries and loads them when building
# the root package's modules, without changing their traces or outputs
# ---

if [ "$UNAME" != Linux ]; then
  echo "native dependency libraries are only supported on Linux"
  exit 0
fi

export XDG_CACHE_HOME=$PWD/cache
unset LEAN_DEV LEAN_DEV_CHECK

# The command of `dep` runs with the native library of `dep` loaded, while `dep2` refers to a
# symbol that no library defines and thus uses the interpreter
LEAN_DEV_NATIVE=1 test_out "native: true, sum: 2.000000" build
match_text "Built dep:native" produced.out
match_text "native code of 'dep2' is unavailable, using the interpreter: " produced.out
match_pat "undefined (symbol: |reference to .)devNativeTest_missing" produced.out
lib=$(echo "$PWD"/cache/fast-lean/native/*/*/libnative_dep.so)
test_exp -f "$lib"
echo "? nm -D --defined-only \"$lib\" | grep -w lp_dep_probs"
nm -D --defined-only "$lib" | grep -w lp_dep_probs
match_text "$lib" .lake/build/ir/Root.setup.json
# the outputs of `Root` (but not its trace and setup, which contain its log and the libraries)
outputs=$(ls .lake/build/lib/lean/Root.* .lake/build/ir/Root.c | grep -v '\.\(hash\|trace\)$')
mkdir outputs
for f in $outputs; do cp "$f" outputs/; done

# The libraries are not part of the trace
LEAN_DEV_NATIVE=0 test_run build --no-build

# Building with the interpreter produces the same outputs
rm -rf .lake/build
LEAN_DEV_NATIVE=0 test_out "native: false, sum: 2.000000" build
no_match_text "native code" produced.out
for f in $outputs; do
  test_cmd cmp "outputs/$(basename "$f")" "$f"
done
LEAN_DEV_NATIVE=1 test_run build --no-build

# Libraries are reused from the cache, including the failure to link one
rm -rf .lake/build
LEAN_DEV_NATIVE=1 test_out "native: true, sum: 2.000000" build
no_match_text "Built dep:native" produced.out
match_pat "undefined (symbol: |reference to .)devNativeTest_missing" produced.out

# Cleanup
./clean.sh
