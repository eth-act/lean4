import Lake
open Lake DSL

package test

require dep from "dep"
require dep2 from "dep2"

@[default_target]
lean_lib Root
