import Std.Tactic.BVDecide

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
