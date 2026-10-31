module

public meta import Lean

/-! A command that reports whether it runs with the native library of `dep` loaded. -/

open Lean Elab Command

public meta def prob : Float := 0.75
/-- Boxing the non-ground constant `prob` creates an auxiliary `_boxed_const` declaration. -/
public meta def probs : Array Float := #[prob, prob, 0.5]

/-- Reports whether the native library of this package is loaded, and evaluates `probs`. -/
elab "#native_check" : command => do
  let maps ← IO.FS.readFile "/proc/self/maps"
  logInfo m!"native: {maps.contains "libnative_dep.so"}, sum: {probs.foldl (· + ·) 0}"
