import Lean
/-!
Generating the equation lemmas of a definition by pattern matching does not consume macro scopes,
like with the upstream release, so that it does not change the hygienic names of later declarations
of the module (such as the labels of `sorry`s).
-/
open Lean Elab Command

def f : Nat → Bool → Nat
  | 0, _ => 0
  | n+1, true => f n true
  | n+1, false => n

/-- info: 0 -/
#guard_msgs in
#eval show CommandElabM Unit from do
  let before := (← get).nextMacroScope
  liftTermElabM do discard <| Meta.getEqnsFor? ``f
  logInfo m!"{(← get).nextMacroScope - before}"

/-- info: f.eq_2 (n : Nat) : f n.succ true = f n true -/
#guard_msgs in
#check f.eq_2
