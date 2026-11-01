/-!
Kernel unfolding counts reported by `diagnostics` for `decide +kernel` proofs. The kernel skips
caching some `whnf_core` results for unshared terms, which repeats reductions; with diagnostics
enabled it must keep caching them so the reported counts stay stable.
-/
set_option diagnostics true
set_option diagnostics.threshold 0

def fib : Nat → Nat
  | 0 => 0 | 1 => 1 | n+2 => fib n + fib (n+1)

theorem t1 : (List.range 60).foldl (· + ·) 0 = 1770 := by decide +kernel
theorem t2 : fib 15 = 610 := by decide +kernel
structure P where (a b : Nat)
def sw (p : P) : P := ⟨p.b, p.a⟩
theorem t3 : (Nat.repeat sw 20 ⟨1, 2⟩).a = 1 := by decide +kernel
