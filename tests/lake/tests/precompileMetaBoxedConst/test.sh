#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Tests that auxiliary constants of `meta` code (here, a boxed `Float`) are initialized when the
# precompiled `meta` code runs at compile time, i.e. by the module's `meta` initializer
test_out "Foo/Use.lean:6:0: 2.000000" build Foo
