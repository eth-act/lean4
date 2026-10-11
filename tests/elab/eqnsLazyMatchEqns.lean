import Lean
/-!
Generating the equation lemmas of a definition by pattern matching does not realize the splitter
and equations of its `match` auxiliary definition when the matcher can serve as its own splitter.
They remain available on demand. Also checks the statements of equation lemmas whose generation
splits with abstracted alternatives, or falls back to the regular split.
-/
open Lean Meta

inductive T where
  | a (n : Nat)
  | b (x y : Bool)
  | c

def f (s : Nat) : T → Nat
  | .a n => n + s
  | .b x _ => if x then s else 0
  | .c => s

def matchEqnsRealized (matcher : Name) : MetaM Bool := do
  let env ← getEnv
  return env.contains (mkPrivateName env (matcher ++ `splitter)) ||
    env.contains (mkPrivateName env (matcher ++ `eq_1))

/-- info: false -/
#guard_msgs in
#eval show MetaM Bool from do
  discard <| getEqnsFor? ``f
  matchEqnsRealized `f.match_1

/-- info: f.eq_1 (s n : Nat) : f s (T.a n) = n + s -/
#guard_msgs in
#check f.eq_1

/-- info: f.eq_2 (s : Nat) (x_1 y : Bool) : f s (T.b x_1 y) = if x_1 = true then s else 0 -/
#guard_msgs in
#check f.eq_2

/-- info: f.eq_3 (s : Nat) : f s T.c = s -/
#guard_msgs in
#check f.eq_3

theorem f_b (s : Nat) : f s (.b true false) = s := by
  simp [f]

/--
info: ∀ (motive : T → Sort u_1) (x y : Bool) (h_1 : (n : Nat) → motive (T.a n)) (h_2 : (x y : Bool) → motive (T.b x y))
  (h_3 : Unit → motive T.c),
  (match T.b x y with
    | T.a n => h_1 n
    | T.b x y => h_2 x y
    | T.c => h_3 ()) =
    h_2 x y
---
info: true
-/
#guard_msgs in
#eval show MetaM Unit from do
  let eqns ← Match.getEquationsFor `f.match_1
  logInfo m!"{(← getConstInfo eqns.eqnNames[1]!).type}"
  logInfo m!"{← matchEqnsRealized `f.match_1}"

-- The discriminant equation makes the alternatives depend on the discriminant.
def useEq {a b : T} (_ : a = b) : Nat := 1

def g (t : T) : Nat :=
  match h : t with
  | .a n => n + useEq h
  | .b .. => 2
  | .c => 3

/-- info: g.eq_1 (n : Nat) : g (T.a n) = n + useEq ⋯ -/
#guard_msgs in
#check g.eq_1

/-- info: g.eq_2 (x y : Bool) : g (T.b x y) = 2 -/
#guard_msgs in
#check g.eq_2

-- Overlapping patterns need a dedicated splitter.
def h : Nat → Bool → Nat
  | 0, true => 0
  | _, false => 1
  | n, _ => n

/-- info: h.eq_1 : h 0 true = 0 -/
#guard_msgs in
#check h.eq_1

/-- info: h.eq_2 (x✝ : Nat) : h x✝ false = 1 -/
#guard_msgs in
#check h.eq_2

/--
info: h.eq_3 (x✝ : Nat) (x✝¹ : Bool) (x_4 : x✝¹ = false → False) (x_3 : x✝ = 0 → x✝¹ = true → False) : h x✝ x✝¹ = x✝
-/
#guard_msgs in
#check h.eq_3

-- Nested `match`es in a recursive definition.
def k : List T → Nat
  | [] => 0
  | t :: ts =>
    match t with
    | .a n => n + k ts
    | .b true _ => k ts
    | _ => 1

/-- info: k.eq_1 : k [] = 0 -/
#guard_msgs in
#check k.eq_1

/-- info: k.eq_2 (ts : List T) (n : Nat) : k (T.a n :: ts) = n + k ts -/
#guard_msgs in
#check k.eq_2

/-- info: k.eq_3 (ts : List T) (y : Bool) : k (T.b true y :: ts) = k ts -/
#guard_msgs in
#check k.eq_3

/--
info: k.eq_4 (t : T) (ts : List T) (x_2 : ∀ (n : Nat), t = T.a n → False) (x_3 : ∀ (y : Bool), t = T.b true y → False) :
  k (t :: ts) = 1
-/
#guard_msgs in
#check k.eq_4
