#!/usr/bin/env bash
source ../common.sh

./clean.sh

# ---
# Tests how `script/fast-lean` selects the development toolchain and invokes its Lake
# ---

FAST_LEAN="$(cd ../../../../script && pwd)/fast-lean"
ROOT=$PWD/proj
export ELAN_HOME=$PWD/elan

# A fake development toolchain whose `lake` reports how it was invoked
mkdir -p elan/toolchains/dev-fast-v4.0.0/bin proj/Foo/Bar
cat > elan/toolchains/dev-fast-v4.0.0/bin/lake <<'EOF'
#!/usr/bin/env bash
if [ "$3 $4 $5" = "env printenv LEAN_SRC_PATH" ]; then echo "$FAKE_SRC_PATH"; exit; fi
echo "args: $*"
echo "LEAN_DEV=${LEAN_DEV-<unset>}"
echo "LEAN_DEV_CHECK=${LEAN_DEV_CHECK-}"
echo "ELAN_TOOLCHAIN=$ELAN_TOOLCHAIN"
echo "LAKE=${LAKE-<unset>}"
echo "lean: $(dirname "$(command -v lake)")"
EOF
chmod +x elan/toolchains/dev-fast-v4.0.0/bin/lake
touch proj/lakefile.toml
echo "leanprover/lean4:v4.0.0" > proj/lean-toolchain
export FAKE_SRC_PATH="/nonexistent:$ROOT/src"
unset LEAN_DEV LEAN_DEV_CHECK

OUT=$PWD/produced.out
fast_out() {
  echo '$' fast-lean "$@"
  if "$FAST_LEAN" "$@" >"$OUT" 2>&1; then rc=0; else rc=$?; fi
  cat "$OUT"
  return $rc
}

test_cmd_out "Usage: fast-lean" "$FAST_LEAN" --help

# Outside a project or without a matching toolchain
(cd / && fast_out build) && exit 1
match_text "not inside a Lake project" produced.out
echo "leanprover/lean4:v4.1.0" > proj/lean-toolchain
(cd proj && fast_out build) && exit 1
match_text "no fast toolchain for v4.1.0" produced.out
echo "leanprover/lean4:v4.0.0" > proj/lean-toolchain

# Defaults, toolchain-specific variables, and invocation from a subdirectory
(cd proj/Foo && LAKE=/official/lake fast_out build)
match_text "args: -d $ROOT build" produced.out
match_text "LEAN_DEV=proofs,sat" produced.out
match_pat "^LEAN_DEV_CHECK=$" produced.out
match_text "ELAN_TOOLCHAIN=dev-fast-v4.0.0" produced.out
match_text "LAKE=<unset>" produced.out
match_text "lean: $ELAN_HOME/toolchains/dev-fast-v4.0.0/bin" produced.out
match_text "fast-lean: dev-fast-v4.0.0, LEAN_DEV=proofs,sat" produced.out

# Named modules are checked fully; paths become module names relative to the source directory
(cd proj && LEAN_DEV_CHECK=Extra fast_out build Lib Foo.Bar +Baz src/Qux/Quux.lean:o -o out.json)
match_text "args: -d $ROOT build Lib Foo.Bar +Baz +Qux.Quux:o -o out.json" produced.out
match_text "LEAN_DEV_CHECK=Extra,Foo.Bar,Baz,Qux.Quux" produced.out

# An empty `LEAN_DEV` builds faithfully
(cd proj && LEAN_DEV= fast_out build)
match_pat "^LEAN_DEV=$" produced.out
match_text "fast-lean: dev-fast-v4.0.0, faithful" produced.out

# Other commands are passed through
(cd proj/Foo && fast_out lean Bar.lean -- -DmaxHeartbeats=0)
match_text "args: -d $ROOT lean $ROOT/Foo/Bar.lean -- -DmaxHeartbeats=0" produced.out
(cd proj && fast_out env printenv LEAN_PATH)
match_text "args: -d $ROOT env printenv LEAN_PATH" produced.out

# Cleanup
./clean.sh
