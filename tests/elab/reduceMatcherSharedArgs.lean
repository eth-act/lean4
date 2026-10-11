import Lean
/-!
`reduceMatcher?` must not traverse the arguments of a `match` application as trees: here the
discriminant's fields are terms with exponentially many subterm occurrences but few distinct
subterms.
-/
open Lean Meta

def fst' : Nat × Nat → Nat
  | (a, _) => a

/-- info: true -/
#guard_msgs in
#eval show MetaM Bool from do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let mut e := x
    for _ in [0:64] do
      e := mkApp2 (mkConst ``Nat.add) e e
    let motive := mkLambda `p .default (mkApp2 (mkConst ``Prod [1, 1]) (mkConst ``Nat) (mkConst ``Nat)) (mkConst ``Nat)
    let discr := mkApp4 (mkConst ``Prod.mk [1, 1]) (mkConst ``Nat) (mkConst ``Nat) e e
    let alt ← withLocalDeclD `a (mkConst ``Nat) fun a => withLocalDeclD `b (mkConst ``Nat) fun b =>
      mkLambdaFVars #[a, b] (mkApp2 (mkConst ``Nat.add) a b)
    let .reduced r ← reduceMatcher? (mkApp3 (mkConst ``fst'.match_1 [1]) motive discr alt)
      | return false
    return r == mkApp2 (mkConst ``Nat.add) e e
