/-!
Tests the `dev.skipProofs` and `dev.skipLinters` development options: proofs are replaced by the
`skippedProof` axiom without changing the declarations' signatures or how lemmas unify.
-/

set_option dev.skipProofs true

theorem bogus : 1 = 2 := by decide

/-- info: 'bogus' depends on axioms: [Lean.skippedProof] -/
#guard_msgs in #print axioms bogus

-- `rfl` proofs are kept, `dsimp` needs them
theorem rflThm : 2 + 2 = 4 := rfl

/-- info: 'rflThm' does not depend on any axioms -/
#guard_msgs in #print axioms rflThm

-- skipped proofs are erased at runtime, so evaluation is not refused as with `sorry`
def pos : { n : Nat // n > 0 } := ⟨1, by omega⟩

/-- info: 1 -/
#guard_msgs in #eval pos.val

/-- info: 'pos' depends on axioms: [Lean.skippedProof] -/
#guard_msgs in #print axioms pos

section
variable (n : Nat) (h : 0 < n)

-- the proof may use `h` implicitly, so it is elaborated to determine whether `h` is a parameter
def withHyp : Fin (n + 1) := ⟨1, by omega⟩

/-- info: withHyp (n : Nat) (h : 0 < n) : Fin (n + 1) -/
#guard_msgs in #check withHyp
end

section
variable (k : Nat)

-- a section variable mentioned only by a proof is a parameter as well
def mentionsK : { m : Nat // m = m } := ⟨0, by have := k; rfl⟩

/-- info: mentionsK (k : Nat) : { m // m = m } -/
#guard_msgs in #check mentionsK
end

-- Proof obligations in statements are discharged by matching hypotheses where possible, so `hi`
-- still occurs in the left-hand side and is instantiated by `rw`
theorem getElem_add_zero (xs : Array Nat) (i : Nat) (hi : i < xs.size) : xs[i] + 0 = xs[i] := by
  simp

set_option dev.skipProofs false in
example (xs : Array Nat) (i : Nat) (h : i < xs.size) : xs[i] + 0 = xs[i] := by
  rw [getElem_add_zero]

-- Proofs whose goals contain metavariables are not skipped: here `rfl` determines `n`
def withAutoParam {n : Nat} (m : Nat) (_h : n = m := by rfl) : Nat := n

theorem autoParamInStatement : withAutoParam 3 = 3 := rfl

def autoParamInBody : Nat := withAutoParam 3

def implicitOnly {n : Nat} : Nat := n
def isThree (a : Nat) (_h : a = 3 := by rfl) : Nat := a

-- the metavariable `rfl` assigns occurs only in the value of the `let`
def autoParamViaLet : Nat :=
  let t := implicitOnly
  isThree t

set_option linter.unusedVariables true
set_option dev.skipLinters true

-- no unused variable warnings
def unusedLet (x : Nat) : Nat :=
  let y := x
  0

set_option dev.skipLinters false

-- attributes are applied as usual to declarations with skipped proofs, also in headers
@[simp] theorem simpSkipped (xs : Array Nat) (i : Nat) (_hi : i < xs.size) : xs[i] * 1 = xs[i] := by
  simp

set_option dev.skipProofs false in
example (xs : Array Nat) (i : Nat) (h : i < xs.size) : xs[i] * 1 = xs[i] := by
  simp only [simpSkipped]

class Positive (n : Nat) : Prop where
  pos : 0 < n

@[instance] theorem positiveOne : Positive 1 := ⟨by decide⟩

@[reducible, instance] def finOneInst : Inhabited (Fin 1) := ⟨⟨0, by decide⟩⟩

set_option dev.skipProofs false in
example : Positive 1 := inferInstance

/-- info: 0 -/
#guard_msgs in #eval (default : Fin 1).val
