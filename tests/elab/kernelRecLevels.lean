import Lean
/-!
Regression test for the kernel's cache of recursor rule right-hand sides instantiated with
universe levels: the same recursor rule is reduced at different universe levels within one type
checker and across declarations, and must produce the correctly instantiated reduct each time.
-/
open Lean Elab Command Meta

/-- Build `@List.rec.{lm,0} Nat (fun _ => Sort lm') nil cons xs` with the given minor premises. -/
def listRec (lm : Level) (motiveTy nilV consV xs : Expr) : Expr :=
  mkAppN (.const ``List.rec [lm, .zero])
    #[.const ``Nat [], .lam `x (mkApp (.const ``List [.zero]) (.const ``Nat [])) motiveTy .default, nilV, consV, xs]

def k3 (ihTy body : Expr) : Expr :=
  .lam `a (.const ``Nat []) (.lam `t (mkApp (.const ``List [.zero]) (.const ``Nat [])) (.lam `ih ihTy body .default) .default) .default

run_cmd liftTermElabM do
  let env ← getEnv
  let one := mkNatLit 1
  let xs ← Meta.mkListLit (.const ``Nat []) [one]
  let nilL ← Meta.mkListLit (.const ``Nat []) []
  -- Same recursor (same rule rhs), two different universe instantiations in a single kernel call.
  let ty0 : Expr := .sort (.succ .zero)          -- Type
  let ty1 : Expr := .sort (.succ (.succ .zero))  -- Type 1
  let a := listRec (.succ (.succ .zero)) ty0 (.const ``Nat []) (k3 ty0 (.const ``Bool [])) xs        -- : Type, reduces to Bool
  let b := listRec (.succ (.succ (.succ .zero))) ty1 ty0 (k3 ty1 (.sort (.succ .zero))) xs           -- : Type 1, reduces to Type
  let c := listRec (.succ (.succ (.succ .zero))) ty1 ty0 (k3 ty1 (.sort (.succ .zero))) nilL         -- reduces to Type (nil rule)
  let c' := listRec (.succ (.succ .zero)) ty0 (.const ``Nat []) (k3 ty0 (.const ``Bool [])) nilL     -- reduces to Nat (nil rule)
  let checks : List (String × Expr × Expr × Bool) := [
    ("a=Bool", a, .const ``Bool [], true),
    ("b=Type", b, ty0, true),
    ("a=Nat", a, .const ``Nat [], false),
    ("c=Type", c, ty0, true),
    ("c'=Nat", c', .const ``Nat [], true),
    ("c'=Bool", c', .const ``Bool [], false),
    -- both levels within one type checker: pair of reductions
    ("pair", mkApp2 (.const ``And []) (mkApp3 (.const ``Eq [.succ (.succ .zero)]) ty0 a (.const ``Bool [])) (mkApp3 (.const ``Eq [.succ (.succ (.succ .zero))]) ty1 b ty0),
             mkApp2 (.const ``And []) (mkApp3 (.const ``Eq [.succ (.succ .zero)]) ty0 (.const ``Bool []) (.const ``Bool [])) (mkApp3 (.const ``Eq [.succ (.succ (.succ .zero))]) ty1 ty0 ty0), true),
    ("pair-wrong", mkApp2 (.const ``And []) (mkApp3 (.const ``Eq [.succ (.succ .zero)]) ty0 a (.const ``Bool [])) (mkApp3 (.const ``Eq [.succ (.succ (.succ .zero))]) ty1 b ty0),
             mkApp2 (.const ``And []) (mkApp3 (.const ``Eq [.succ (.succ .zero)]) ty0 (.const ``Bool []) (.const ``Bool [])) (mkApp3 (.const ``Eq [.succ (.succ (.succ .zero))]) ty1 ty0 (.const ``Nat [])), false)
  ]
  for (nm, x, y, expected) in checks do
    match Kernel.isDefEq env {} x y with
    | .ok r => logInfo m!"{nm}: {r} {if r == expected then "OK" else "MISMATCH"}"
    | .error e => logInfo m!"{nm}: error {e.toMessageData {}}"
  -- type check the pair proposition and the terms themselves in the kernel
  for (nm, x) in [("a", a), ("b", b), ("c", c)] do
    match Kernel.check env {} x with
    | .ok t => logInfo m!"check {nm} : {t}"
    | .error e => logInfo m!"check {nm}: error {e.toMessageData {}}"

-- Kernel-checked declarations that reduce the same recursor at two universe levels.
theorem t1 : (@List.rec.{2,0} Nat (fun _ => Type) Nat (fun _ _ _ => Bool) [1] = Bool) ∧
             (@List.rec.{3,0} Nat (fun _ => Type 1) Type (fun _ _ _ => Type) [1] = Type) := ⟨rfl, rfl⟩
