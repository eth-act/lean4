# fast-lean

Faster Lean builds for development. `fast-lean build` instead of `lake build` while iterating;
plain `lake build` (the official toolchain) when you are done, which re-checks everything fast-lean
built.

## Install

Requires [elan](https://github.com/leanprover/elan), bash and curl.

```sh
curl -sSfL https://raw.githubusercontent.com/eth-act/lean4/fast-lean-dist/install.sh | sh
```

This only installs the `fast-lean` script. On first use in a project, fast-lean installs the fast
toolchain for the project's Lean version (from the `lean-toolchain` file) with elan. Projects on a
Lean version without a fast toolchain are built with plain `lake`, with a note.

## Use

```sh
fast-lean build                 # like `lake build`, with development shortcuts
fast-lean build My.Module       # check My.Module fully, take shortcuts in its dependencies
fast-lean lean My/Module.lean   # like `lake lean`
lake build                      # official toolchain: re-checks everything fast-lean built
```

`fast-lean --help` describes the shortcuts (`LEAN_DEV`) and guarantees.

## Supported Lean versions

`versions.txt` maps each supported Lean version to its fast toolchain, an elan toolchain built by
the CI of [eth-act/lean4](https://github.com/eth-act/lean4) from the `dev-fast-<version>` branches.
The script itself lives in those branches as `script/fast-lean`.
