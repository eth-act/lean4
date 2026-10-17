import Lake
open Lake DSL

package test

@[default_target]
lean_lib Foo

lean_exe foo where
  root := `Main
