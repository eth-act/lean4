#!/usr/bin/env bash
source ../common.sh

./clean.sh

# ---
# Tests that this (development) Lake marks the traces of the outputs it builds, so that an
# official toolchain never reuses them, while it reuses outputs with an official trace.
# ---

unset LEAN_DEV LEAN_DEV_CHECK

TRACE=.lake/build/lib/lean/Foo.trace
saved_hash() { sed -n 's/.*"depHash": *"\([0-9a-f]*\)".*/\1/p' "$TRACE"; }
# the trace hash an official toolchain computes
plain_hash() { "$LAKE" query +Foo:depHash; }
fake_official() {
  sed_i "s/\"depHash\": *\"[0-9a-f]*\"/\"depHash\": \"$(plain_hash)\"/" "$TRACE"
}

# A build marks the trace, and marked traces are stable
test_out "Built Foo" build
test_exp -n "$(saved_hash)"
test_exp "$(saved_hash)" != "$(plain_hash)"
MARKED=$(saved_hash)
test_run build --no-build

# Outputs with an official trace are reused as is, also with dev options and exemptions
fake_official
test_run build --no-build
test_not_out "Built Foo" build
test_exp "$(saved_hash)" = "$(plain_hash)"
LEAN_DEV=proofs test_run build --no-build
LEAN_DEV=proofs LEAN_DEV_CHECK=Foo test_run build --no-build

# An official trace without outputs is not trusted
test_cmd rm .lake/build/lib/lean/Foo.olean
test_out "Built Foo" build
test_exp "$(saved_hash)" = "$MARKED"

# Outputs built without dev options are reused by builds with them
LEAN_DEV=proofs test_run build --no-build

# Rebuilds with dev options mix them into the trace on top of the marker
test_cmd rm .lake/build/lib/lean/Foo.olean
LEAN_DEV=proofs test_out "Built Foo" build
test_exp "$(saved_hash)" != "$MARKED"
test_exp "$(saved_hash)" != "$(plain_hash)"
LEAN_DEV=proofs test_run build --no-build
test_fails build --no-build
LEAN_DEV=proofs LEAN_DEV_CHECK=Foo test_fails build --no-build
test_out "Built Foo" build
test_exp "$(saved_hash)" = "$MARKED"

# The artifact cache only receives outputs under the marked trace hash
test_cmd rm -rf .lake/build
export LAKE_CACHE_DIR="$PWD/.lake/cache" LAKE_ARTIFACT_CACHE=true
test_out "Built Foo" build
test_exp "$(saved_hash)" = "$MARKED"
test_exp -n "$(find .lake/cache/outputs -name "$MARKED.json")"
test_exp -z "$(find .lake/cache/outputs -name "$(plain_hash).json")"
unset LAKE_CACHE_DIR LAKE_ARTIFACT_CACHE

# Native artifacts are marked as well
test_run build foo
test_cmd grep -F '"dev toolchain"' "$(find .lake/build/bin -name 'foo*.trace')"

# Configurations elaborated by this toolchain are marked, while official ones are reused
CONFIG_TRACE=$(find .lake -name lakefile.olean.trace)
test_cmd grep -F '+dev"' "$CONFIG_TRACE"
sed_i 's/+dev"/"/' "$CONFIG_TRACE"
test_run build --no-build
test_cmd_fails grep -F '+dev"' "$CONFIG_TRACE"
test_run build --no-build -R
test_cmd grep -F '+dev"' "$CONFIG_TRACE"

# Cleanup
rm -f produced.out
