import Lean
/-!
Regression test for the kernel's specialized bound-variable traversal used by `Expr.instantiate`,
`instantiateRev`, `instantiateRange`, `instantiateRevRange`, `liftLooseBVars` and
`lowerLooseBVars`. Random expressions with shared subterms are transformed and serialized together
with their pointer-sharing structure; the hash of all results was recorded with the previous
generic `replace`-based implementation, so it checks that results, including physical sharing,
are unchanged.
-/
open Lean


structure G where s : UInt64

abbrev M := StateM G

def rnd (n : Nat) : M Nat := do
  let g ← get
  let s := g.s * 6364136223846793005 + 1442695040888963407
  set (G.mk s)
  return (s >>> 33).toNat % n

def leaf : M Expr := do
  match ← rnd 8 with
  | 0 => return .sort (if (← rnd 2) == 0 then .zero else .param `u)
  | 1 => return .const `c [.param `u, .succ .zero]
  | 2 => return .lit (.natVal (← rnd 100))
  | 3 => return .lit (.strVal "s")
  | 4 => return .fvar ⟨`x⟩
  | 5 => return .mvar ⟨`m⟩
  | _ => return .bvar (← rnd 7)

def pick (pool : Array Expr) : M Expr := do
  if pool.isEmpty || (← rnd 5) == 0 then leaf
  else
    -- bias towards recent entries for depth, but allow old ones for sharing
    let i ← rnd pool.size
    return pool[i]!

def node (pool : Array Expr) : M Expr := do
  match ← rnd 7 with
  | 0 | 1 => return .app (← pick pool) (← pick pool)
  | 2 => return .lam `x (← pick pool) (← pick pool) .default
  | 3 => return .forallE `y (← pick pool) (← pick pool) .implicit
  | 4 => return .letE `z (← pick pool) (← pick pool) (← pick pool) ((← rnd 2) == 0)
  | 5 => return .mdata {} (← pick pool)
  | _ => return .proj `S (← rnd 3) (← pick pool)

def build (n : Nat) : M (Array Expr) := do
  let mut pool := #[]
  for _ in [0:n] do
    pool := pool.push (← node pool)
  return pool

unsafe def serCore (e : Expr) : StateT (Std.HashMap USize Nat) (StateM String) Unit := do
  let p := ptrAddrUnsafe e
  if let some i := (← get)[p]? then
    modify fun (m : Std.HashMap USize Nat) => m
    modifyThe String (· ++ s!"#{i}")
    return
  let i := (← get).size
  modify (·.insert p i)
  modifyThe String (· ++ s!"[{i}:")
  match e with
  | .bvar n => modifyThe String (· ++ s!"b{n}")
  | .fvar f => modifyThe String (· ++ s!"f{f.name}")
  | .mvar m => modifyThe String (· ++ s!"m{m.name}")
  | .sort l => modifyThe String (· ++ s!"S{l}")
  | .const n ls => modifyThe String (· ++ s!"C{n}{ls}")
  | .lit (.natVal v) => modifyThe String (· ++ s!"N{v}")
  | .lit (.strVal v) => modifyThe String (· ++ s!"T{v}")
  | .app f a => modifyThe String (· ++ "A "); serCore f; serCore a
  | .lam n t b bi => modifyThe String (· ++ s!"L{n}{repr bi} "); serCore t; serCore b
  | .forallE n t b bi => modifyThe String (· ++ s!"P{n}{repr bi} "); serCore t; serCore b
  | .letE n t v b nd => modifyThe String (· ++ s!"Z{n}{nd} "); serCore t; serCore v; serCore b
  | .mdata _ b => modifyThe String (· ++ "D "); serCore b
  | .proj s i b => modifyThe String (· ++ s!"J{s}{i} "); serCore b
  modifyThe String (· ++ "]")

/-- Serialize a list of expressions with a shared pointer table: captures structure, binder data
and which subterms are physically shared (also with the inputs). -/
unsafe def serImpl (es : List Expr) : String :=
  let act : StateT (Std.HashMap USize Nat) (StateM String) Unit := es.forM fun e => do
    serCore e; modifyThe String (· ++ "|")
  ((act.run {}).run "").2

@[implemented_by serImpl] opaque ser (es : List Expr) : String

def checkCase (pool : Array Expr) : M (String × String) := do
  let e ← pick pool
  let k ← rnd 7
  let nsub ← rnd 5
  let mut subst := #[]
  for _ in [0:nsub] do subst := subst.push (← pick pool)
  match k with
  | 0 => let r := e.instantiate subst; return ("inst", ser ([e, r] ++ subst.toList))
  | 1 => let v ← pick pool; let r := e.instantiate1 v; return ("inst1", ser [e, v, r])
  | 2 => let r := e.instantiateRev subst; return ("instRev", ser ([e, r] ++ subst.toList))
  | 3 =>
    let b ← rnd (subst.size + 1); let en := b + (← rnd (subst.size + 1 - b))
    let r := e.instantiateRange b en subst
    let r2 := e.instantiateRevRange b en subst
    return ("instRange", ser ([e, r, r2] ++ subst.toList))
  | 4 => let s ← rnd 6; let d ← rnd 4; let r := e.liftLooseBVars s d; return ("lift", ser [e, r])
  | 5 => let d ← rnd 3; let s := d + (← rnd 4); let r := e.lowerLooseBVars s d; return ("lower", ser [e, r])
  | _ =>
    -- nested binders: instantiate under abstraction to exercise offsets
    let r := (Expr.lam `w e e .default).instantiate subst
    return ("instLam", ser ([e, r] ++ subst.toList))

def mix (h : UInt64) (s : String) : UInt64 := mixHash h (hash s)

def runCases (rounds : Nat) : Nat × UInt64 := Id.run do
  let mut h : UInt64 := 7
  let mut g : G := ⟨12345⟩
  let mut total := 0
  for rd in [0:rounds] do
    let (pool, g') := (build (20 + rd % 200)).run g
    g := g'
    for _ in [0:50] do
      let ((nm, s), g') := (checkCase pool).run g
      g := g'
      h := mix h nm
      h := mix h s
      total := total + 1
  return (total, h)

#eval runCases 60
