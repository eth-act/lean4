import Std.Tactic.BVDecide
import Lean.Elab.Tactic.Basic

/-!
Tests the `dev.trustSat` development option: `bv_decide` trusts the SAT solver's UNSAT answer instead
of checking an LRAT certificate, but still reports counterexamples.
-/

set_option dev.trustSat true

theorem trusted (x y : BitVec 8) : (x &&& y) + (x ||| y) = x + y := by
  bv_decide

/--
info: 'trusted' depends on axioms: [propext, Classical.choice, Lean.skippedProof, Quot.sound]
-/
#guard_msgs in #print axioms trusted

/-- error: The prover found a counterexample, consider the following assignment: -/
#guard_msgs (substring := true) in
example (x y : BitVec 4) : x * y = x + y := by
  bv_decide

/-! `bv_decide?` still checks the certificate, as the `bv_check` it suggests replays it. -/

open Lean Elab Tactic in
/-- `bv_decide?` writes the certificate next to the file, which needs an absolute file name. -/
elab "with_absolute_file_name " t:tactic : tactic => do
  let fileName := (← IO.currentDir) / "devTrustSat.lean"
  withTheReader Core.Context ({ · with fileName := fileName.toString }) (evalTactic t)

/--
info: Try this:
  [apply] bv_check "devTrustSat.lean-certified-38-26.lrat"
-/
#guard_msgs in
theorem certified (x y : BitVec 8) : (x &&& y) + (x ||| y) = x + y := by
  with_absolute_file_name bv_decide?

/--
info: 'certified' depends on axioms: [propext, Classical.choice, Quot.sound, certified._native.bv_decide.ax_1_5]
-/
#guard_msgs in #print axioms certified

#eval IO.FS.removeFile "devTrustSat.lean-certified-38-26.lrat"
