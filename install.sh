#!/bin/sh
# Installs `fast-lean` into ~/.local/bin (or $FAST_LEAN_BIN_DIR):
#   curl -sSfL https://raw.githubusercontent.com/eth-act/lean4/fast-lean-dist/install.sh | sh
# Fast toolchains themselves are installed with elan on first use, per Lean version.
set -eu

src=${FAST_LEAN_SRC:-https://raw.githubusercontent.com/eth-act/lean4/dev-fast-v4.34.0/script/fast-lean}
bindir=${FAST_LEAN_BIN_DIR:-$HOME/.local/bin}

if ! command -v elan >/dev/null 2>&1; then
  echo "fast-lean needs elan; install it first: https://github.com/leanprover/elan#installation" >&2
  exit 1
fi
if ! command -v bash >/dev/null 2>&1 || ! command -v curl >/dev/null 2>&1; then
  echo "fast-lean needs bash and curl" >&2
  exit 1
fi

mkdir -p "$bindir"
curl -sSfL "$src" -o "$bindir/fast-lean.tmp"
chmod +x "$bindir/fast-lean.tmp"
mv "$bindir/fast-lean.tmp" "$bindir/fast-lean"
echo "installed $bindir/fast-lean"

case ":$PATH:" in
  *":$bindir:"*) ;;
  *) echo "note: $bindir is not on PATH; add it to use \`fast-lean\`" >&2 ;;
esac
echo "usage: run \`fast-lean build\` instead of \`lake build\` in a Lean project; \`fast-lean --help\` for details"
