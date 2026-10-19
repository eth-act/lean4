import Lean
open Lean

/-!
Checks that the compiler-relevant `.olean` data of a toolchain is a conservative extension of that
of another one, so that `.olean` files built by the latter (an official release) can be used with
the former (a development build identifying as that release).

Downstream modules refer to core declarations by name in their IR and LCNF, including
compiler-generated auxiliary declarations (`_at_`, `spec_`, `_lam_`, `_closed_`, `_redArg`, ...),
inline core LCNF bodies, and reuse the specialization cache of the core library. Hence every entry
of the reference toolchain must exist in the checked one with the same signature and, unless the
declaration is allowlisted, the same body. Compared are IR declarations, base and mono phase LCNF
declarations, impure signatures, specialization information, specialization cache entries, and
function summaries.

Bodies are compared after canonicalizing the effects of different fresh variable indices (order of
join point parameters, variable names, order of reference counting instructions). Differences only
in source positions (of `panic!` etc. and builtin declaration ranges) are reported but accepted.

Usage (compile with `lean -c` and `leanc` for speed; reads both directories' `.olean` files):
* `compilerABI check <ref olean dir> <new olean dir> <allowlist> <module>...` reports differences per
  module and fails on errors. `<prefix>.*` stands for all modules with that prefix.
* `compilerABI (show | show-canonical) <olean dir> <kind> <key> <module>...` prints entries.
* `compilerABI list <olean dir> <kind> <module>` prints the keys of a module's entries of a kind.

Allowlist lines are `<declaration name>  # reason`. Compiler-generated auxiliary declarations may
only be listed with an explicit `aux ` prefix.
-/

namespace CompilerABI

unsafe def findExt (n : Name) : IO (PersistentEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState) := do
  for ext in (← persistentEnvExtensionsRef.get) do
    if privateToUserName ext.name == n then
      return ext
  throw <| IO.userError s!"environment extension {n} not found"

unsafe def entries (α) (env : Environment) (n : Name) (modIdx : Nat) : IO (Array α) := do
  let ext ← findExt n
  return unsafeCast (ext.getModuleEntries env modIdx)

/-- Formats without line breaks, which the canonicalization below relies on. -/
def wide (f : Format) : String :=
  f.pretty (width := 1000000)

def irSig (d : IR.Decl) : String :=
  let ps := d.params.toList.map fun p => (if p.borrow then "@& " else "") ++ toString p.ty
  s!"{ps} -> {d.resultType}"

/-- All entries of module `i` as `(kind, key, sig, body)`, with unhashed `sig` and `body`. -/
unsafe def moduleEntries (env : Environment) (i : Nat) : CoreM (Array (String × String × String × String)) := do
  let mut out := #[]
  for d in IR.declMapExt.getModuleEntries env i do
    out := out.push ("ir", toString d.name, irSig d, wide (format d))
  for d in IR.declMapExt.getModuleIREntries env i do
    out := out.push ("irx", toString d.name, irSig d, wide (format d))
  for (kind, ext, phase) in [("base", Compiler.LCNF.baseExt, Compiler.LCNF.Phase.base),
      ("mono", Compiler.LCNF.monoExt, .mono)] do
    for d in ext.getModuleEntries env i do
      let fmt ← Compiler.LCNF.ppDecl' d phase
      out := out.push (kind, toString d.name, d.type.dbgToString, wide fmt)
  for s in Compiler.LCNF.impureSigExt.getModuleEntries env i do
    out := out.push ("impureSig", toString s.name, s.type.dbgToString,
      toString (s.params.map fun p => (p.type.dbgToString, p.borrow)) ++ toString s.safe)
  for e in Compiler.LCNF.specExtension.getModuleEntries env i do
    out := out.push ("specInfo", toString e.declName, "", reprStr e.paramsInfo ++ toString e.alreadySpecialized)
  for e in ← entries Compiler.LCNF.Specialize.CacheEntry env `Lean.Compiler.LCNF.Specialize.specCacheExt i do
    -- `Expr.hash` is invariant under alpha-renaming like the cache lookup
    let debug := (← IO.getEnv "COMPILER_ABI_DEBUG").isSome
    out := out.push ("specCache", s!"{String.ofList (Nat.toDigits 16 (hash e.key).toNat)} {e.declName}", "",
      if debug then e.key.dbgToString else "")
  for (n, v) in Compiler.LCNF.UnreachableBranches.functionSummariesExt.getModuleEntries env i do
    out := out.push ("summary", toString n, "", reprStr v)
  return out

def isDigit' (c : Char) : Bool := c.isDigit

/-! `List Char`-based string helpers, as the `String` API differs between the supported versions. -/

def sdrop (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)
def stake (s : String) (n : Nat) : String := String.ofList (s.toList.take n)
def sdropRight (s : String) (n : Nat) : String := String.ofList (s.toList.take (s.length - n))
def strim (s : String) : String :=
  String.ofList ((s.toList.dropWhile (·.isWhitespace)).reverse.dropWhile (·.isWhitespace)).reverse

/-- Functions whose `Nat` arguments are source positions (`panic!`, `unreachable!`, etc.). -/
def panicFns : List String :=
  ["mkPanicMessageWithDecl", "mkPanicMessage", "panicWithPosWithDecl", "panicWithPos"]

/-- Splits at spaces, semicolons and parentheses; uses only `List Char` for portability. -/
def tokens (l : String) : List String :=
  let rec go : List Char → List Char → List String
    | [], acc => if acc.isEmpty then [] else [String.ofList acc.reverse]
    | c :: cs, acc =>
      if c == ' ' || c == ';' || c == '(' || c == ')' then
        if acc.isEmpty then go cs [] else String.ofList acc.reverse :: go cs []
      else go cs (c :: acc)
  go l.toList []

/--
Masks source positions in a formatted IR or LCNF body: literals bound to variables that are passed
to `panicFns`, and all literals of builtin declaration range registrations. These only change when
lines are added or removed above the declaration in its source file.
-/
def maskPositions (name body : String) : String := Id.run do
  let lines := body.splitOn "\n"
  let mut posVars : Std.HashSet String := {}
  for l in lines do
    let toks := tokens l
    if toks.any (panicFns.contains ·) then
      for t in toks do
        posVars := posVars.insert t
  let all := (name.splitOn ".").any (·.startsWith "declRange")
  let mut out := #[]
  for l in lines do
    let l' := match l.splitOn " := " with
      | [lhs, rhs] =>
        match tokens lhs, tokens rhs with
        | "let" :: v :: _, [lit] =>
          if lit.toList.all isDigit' && (all || posVars.contains v) then s!"{lhs} := N;" else l
        | _, _ => l
      | _ => l
    out := out.push l'
  return "\n".intercalate out.toList

def isIdChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == '\'' || c == '?' || c == '!'

/-- Applies `f` to the maximal runs of `isIdChar` characters of `l`. -/
def mapIds (l : String) (f : String → String) : String :=
  let rec go : List Char → List Char → String → String
    | [], acc, out => if acc.isEmpty then out else out ++ f (String.ofList acc.reverse)
    | c :: cs, acc, out =>
      if isIdChar c then go cs (c :: acc) out
      else
        let out := if acc.isEmpty then out else out ++ f (String.ofList acc.reverse)
        go cs [] (out.push c)
  go l.toList [] ""

def ids (l : String) : Array String := Id.run do
  let mut out := #[]
  let rec go : List Char → List Char → Array String → Array String
    | [], acc, out => if acc.isEmpty then out else out.push (String.ofList acc.reverse)
    | c :: cs, acc, out =>
      if isIdChar c then go cs (c :: acc) out
      else go cs [] (if acc.isEmpty then out else out.push (String.ofList acc.reverse))
  out := go l.toList [] out
  return out

/--
Local variable and join point names: `x_<n>`/`block_<n>` in IR, `<name>.<n>` (a single component
with a numeric suffix) in LCNF.
-/
def localName? (s : String) : Option String :=
  match s.splitOn "." with
  | [p, n] => if !p.isEmpty && !n.isEmpty && n.toList.all isDigit' && !p.toList.head!.isDigit then some (p ++ ".") else none
  | [s] =>
    match s.splitOn "_" with
    | [p, n] => if (p == "x" || p == "block") && !n.isEmpty && n.toList.all isDigit' then some (p ++ "_") else none
    | _ => none
  | _ => none

def indentOf (l : String) : Nat :=
  (l.toList.takeWhile (· == ' ')).length

def trimLeft' (l : String) : String :=
  String.ofList (l.toList.dropWhile (· == ' '))

def isRcLine (l : String) : Bool :=
  let t := trimLeft' l
  t.startsWith "inc " || t.startsWith "dec "

/-- Splits at spaces outside of parentheses. -/
def splitTop (s : String) : List String :=
  let rec go : List Char → Nat → List Char → List String
    | [], _, acc => if acc.isEmpty then [] else [String.ofList acc.reverse]
    | c :: cs, d, acc =>
      if c == ' ' && d == 0 then
        if acc.isEmpty then go cs d [] else String.ofList acc.reverse :: go cs d []
      else go cs (if c == '(' then d + 1 else if c == ')' then d - 1 else d) (c :: acc)
  go s.toList 0 []

/--
Parses a join point header: IR `block_<n> (x_<i> : ty)... :=` or LCNF `jp _jp.<n> x.<i>... : ty :=`.
Returns the join point name, the text before and after the parameters, and the parameters.
-/
def jpHeader? (l : String) : Option (String × String × String × List String) := do
  let ind := String.ofList (List.replicate (indentOf l) ' ')
  let t := trimLeft' l
  guard <| t.endsWith ":="
  if t.startsWith "block_" then
    let name :: _ := t.splitOn " " | none
    let ps := sdropRight (sdrop t (name.length + 1)) 3
    let ps := if t == name ++ " :=" then [] else splitTop ps
    return (name, ind ++ name, " :=", ps)
  else if t.startsWith "jp " then
    let rest := sdrop t 3
    let name :: _ := rest.splitOn " " | none
    let rest := sdrop rest (name.length + 1)
    let ps :: tys := rest.splitOn " : " | none
    return (name, ind ++ "jp " ++ name, " : " ++ " : ".intercalate tys, splitTop ps)
  else none

def paramVar (p : String) : String :=
  (ids p)[0]?.getD p

def permute (xs : List String) (perm : Array Nat) : List String :=
  perm.toList.map fun i => xs[i]!

structure Line where
  text : String
  indent : Nat
  ids : Array String
  rc : Bool
  deriving Inhabited

def mkLine (text : String) : Line :=
  { text, indent := indentOf text, ids := ids text, rc := isRcLine text }

/-- Permutes the arguments of a jump `jmp`/`goto` line. -/
def permuteJump (l : String) (perm : Array Nat) : String :=
  let t := trimLeft' l
  let semi := t.endsWith ";"
  let t' := if semi then sdropRight t 1 else t
  match t'.splitOn " " with
  | kw :: j :: args =>
    if args.length == perm.size then
      String.ofList (List.replicate (indentOf l) ' ') ++ " ".intercalate (kw :: j :: permute args perm) ++
        (if semi then ";" else "")
    else l
  | _ => l

def isJpHeaderStart (l : Line) : Bool :=
  l.ids.size ≥ 2 && (l.ids[0]!.startsWith "block_" || l.ids[0]! == "jp")

/-- Orders the parameters of each join point by their first use in its body. -/
def sortJpParams (lines : Array Line) : Array Line := Id.run do
  let mut lines := lines
  let mut jumps : Std.HashMap String (Array Nat) := {}
  for h : i in [0:lines.size] do
    let l := lines[i]
    if l.ids.size ≥ 2 && (l.ids[0]! == "jmp" || l.ids[0]! == "goto") then
      jumps := jumps.insert l.ids[1]! ((jumps.getD l.ids[1]! #[]).push i)
  for i in (List.range lines.size).reverse do
    let l := lines[i]!
    unless isJpHeaderStart l do continue
    let some (jp, pre, post, ps) := jpHeader? l.text | continue
    if ps.length < 2 then continue
    let vars := ps.map paramVar
    let mut pos : Std.HashMap String Nat := {}
    let mut n := 0
    let mut j := i + 1
    while j < lines.size && lines[j]!.indent > l.indent && pos.size < vars.length do
      let b := lines[j]!
      j := j + 1
      if b.rc then continue
      for x in b.ids do
        if !pos.contains x && vars.contains x then pos := pos.insert x n
        n := n + 1
    let keys := vars.toArray.mapIdx fun k v => (pos.getD v (1000000 + k), k)
    let perm := (keys.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)).map (·.2)
    if perm == Array.range ps.length then continue
    lines := lines.set! i (mkLine (pre ++ String.join ((permute ps perm).map (" " ++ ·)) ++ post))
    for k in jumps.getD jp #[] do
      lines := lines.set! k (mkLine (permuteJump lines[k]!.text perm))
  return lines

/--
Canonicalizes a formatted IR or LCNF body up to the effects of different fresh variable indices
in the compiler: the order of join point parameters, the names of local variables, and the order
of consecutive reference count instructions.
-/
def canonicalize (body : String) : String := Id.run do
  let mut lines := (body.splitOn "\n").toArray.map mkLine
  -- jumps pass parameters on to other join points, so iterate until their order is stable
  if lines.any isJpHeaderStart then
    for _ in [0:20] do
      let lines' := sortJpParams lines
      if lines'.map (·.text) == lines.map (·.text) then break
      lines := lines'

  let mut names : Std.HashMap String String := {}
  let mut out := #[]
  for l in lines.map (·.text) do
    let mut l' := ""
    for x in ids l do
      if let some p := localName? x then
        unless names.contains x do
          names := names.insert x s!"{p}{names.size}"
    l' := mapIds l fun x => names.getD x x
    out := out.push l'
  -- sort runs of `inc`/`dec` lines
  let mut res := #[]
  let mut i := 0
  while i < out.size do
    let l := out[i]!
    if isRcLine l then
      let kw := stake (trimLeft' l) 4
      let mut j := i
      while j < out.size && isRcLine out[j]! && stake (trimLeft' out[j]!) 4 == kw && indentOf out[j]! == indentOf l do
        j := j + 1
      res := res ++ (out[i:j].toArray.qsort (· < ·))
      i := j
    else
      res := res.push l
      i := i + 1
  return "\n".intercalate res.toList

/--
Expands `<prefix>.*` into all modules with that prefix (and `<prefix>` itself) in the `.olean`
directory `root`.
-/
def expandMods (root : System.FilePath) (mods : List String) : IO (Array Name) := do
  let mut out := #[]
  for m in mods do
    if m.endsWith ".*" then
      let pre := sdropRight m 2
      let preName := pre.toName
      if ← (root / (pre ++ ".olean")).pathExists then
        out := out.push preName
      let dir := root / System.mkFilePath (pre.splitOn ".")
      if ← dir.isDir then
        for f in ← dir.walkDir do
          if f.extension == some "olean" then
            let some rel := (f.withExtension "").toString.dropPrefix? (root.toString ++ "/") | continue
            out := out.push (rel.toString.splitOn "/" |>.foldl (·.str ·) .anonymous)
    else
      out := out.push m.toName
  return out.qsort Name.lt

/-- Imports `mods` (see `expandMods`) from the `.olean` directory `root`. -/
def importAll (root : System.FilePath) (mods : List String) : IO Environment := do
  searchPathRef.set [root]
  let imports := (← expandMods root mods).map fun m => { module := m : Import }
  importModules imports {} (level := .private)

def runCore (env : Environment) (x : CoreM α) : IO α :=
  -- `pp.raw` avoids the delaborator; fresh names are deterministic as `ppDecl'` restores the state
  let options := pp.explicit.set (pp.raw.set {} true) true
  Prod.fst <$> x.toIO { fileName := "<CompilerABI>", fileMap := default, maxHeartbeats := 0, options } { env }

/-- Name components introduced by the compiler for auxiliary declarations. -/
def isAuxName (n : String) : Bool :=
  (n.splitOn ".").any fun c =>
    c == "_redArg" || c == "_boxed" || c == "_at_" || c.startsWith "spec_" ||
    c.startsWith "_lam_" || c.startsWith "_closed_" || c.startsWith "_elam_" || c.startsWith "_spec"

/-- Difference categories; only the first three are errors. -/
def categories : List String :=
  ["missing", "signature changed", "body changed", "allowlisted body changed",
    "source positions changed", "equivalent body", "specialization key changed", "moved"]

structure Report where
  diffs : Std.HashMap String (Array String) := {}
  added : Nat := 0

def Report.push (r : Report) (cat what : String) : Report :=
  { r with diffs := r.diffs.insert cat ((r.diffs.getD cat #[]).push what) }

def Report.count (r : Report) (cat : String) : Nat :=
  (r.diffs.getD cat #[]).size

def Report.errors (r : Report) : Nat :=
  categories.take 3 |>.foldl (· + r.count ·) 0

def Report.summary (r : Report) : String :=
  ", ".intercalate (categories.map fun c => s!"{r.count c} {c}") ++ s!", {r.added} added"

/-- An entry with hashes of its formatted signature and body. -/
structure Entry where
  mod : Nat
  sig : UInt64
  body : UInt64

abbrev Index := Std.HashMap (String × String) Entry

unsafe def index (env : Environment) : IO Index :=
  runCore env do
    let mut m := {}
    for i in [0:env.header.moduleNames.size] do
      for (kind, key, sig, body) in ← moduleEntries env i do
        m := m.insert (kind, key) { mod := i, sig := sig.hash, body := body.hash }
    return m

def readAllowlist (path : System.FilePath) : IO (Std.HashSet String × Nat) := do
  let mut allow := {}
  let mut errors := 0
  for line in (← IO.FS.lines path) do
    let line := strim (line.splitOn "#")[0]!
    if line.isEmpty then continue
    let (aux, n) := if line.startsWith "aux " then (true, strim (sdrop line 4)) else (false, line)
    if isAuxName n && !aux then
      IO.eprintln s!"error: allowlisted auxiliary declaration {n} must be marked 'aux' and justified"
      errors := errors + 1
    allow := allow.insert n
  return (allow, errors)

/--
Compares the modules `mods` (and their imports) in the `.olean` directories `refRoot` and `newRoot`
and prints a report per module. Returns the number of errors.
-/
unsafe def check (refRoot newRoot allowPath : System.FilePath) (mods : List String) : IO Nat := do
  let (allow, allowErrors) ← readAllowlist allowPath
  let refEnv ← importAll refRoot mods
  let newEnv ← importAll newRoot mods
  let ref ← index refEnv
  let new ← index newEnv
  let refMod (e : Entry) := refEnv.header.moduleNames[e.mod]!
  let newMod (e : Entry) := newEnv.header.moduleNames[e.mod]!
  let mut reports : Std.HashMap Name Report := {}
  -- entries whose bodies differ, by module, to be compared in detail below
  let mut bodyDiffs : Std.HashMap (Nat × Nat) (Array (String × String)) := {}
  let mut usedAllow : Std.HashSet String := {}
  let lambdaParents : Std.HashSet String := allow.fold (init := {}) fun s n =>
    match n.splitOn "._lam_" with
    | p :: _ :: _ => s.insert p |>.insert (p.splitOn "._redArg")[0]!
    | _ => s
  -- Specialization keys contain the code of local functions, including source positions. Hence a
  -- key may change while the specialization it maps to stays the same.
  let specName (key : String) := sdrop key ((key.splitOn " ")[0]!.length + 1)
  let newSpecNames : Std.HashSet String := new.fold (init := {}) fun s (kind, key) _ =>
    if kind == "specCache" then s.insert (specName key) else s
  for ((kind, key), e) in ref do
    let mut r := reports.getD (refMod e) {}
    let what := s!"{kind} {key}"
    match new[(kind, key)]? with
    | none =>
      if kind == "specCache" && newSpecNames.contains (specName key) then
        r := r.push "specialization key changed" what
      else
        r := r.push "missing" what
    | some e' =>
      if newMod e' != refMod e then
        r := r.push "moved" s!"{what} -> {newMod e'}"
      if e'.sig != e.sig then
        r := r.push "signature changed" what
      else if e'.body != e.body then
        if allow.contains key then
          usedAllow := usedAllow.insert key
          r := r.push "allowlisted body changed" what
        else if (kind == "base" || kind == "mono") && lambdaParents.contains key then
          -- before lambda lifting, the allowlisted lambda is part of this declaration
          r := r.push "allowlisted body changed" what
        else
          bodyDiffs := bodyDiffs.insert (e.mod, e'.mod) ((bodyDiffs.getD (e.mod, e'.mod) #[]).push (kind, key))
    reports := reports.insert (refMod e) r
  for ((kind, key), e') in new do
    unless ref.contains (kind, key) do
      let r := reports.getD (newMod e') {}
      reports := reports.insert (newMod e') { r with added := r.added + 1 }
  for ((refIdx, newIdx), keys) in bodyDiffs do
    let keySet : Std.HashSet (String × String) := Std.HashSet.ofArray keys
    let entriesOf (env : Environment) (i : Nat) : IO (Std.HashMap (String × String) (String × String)) :=
      runCore env do
        let mut m := {}
        for (kind, key, _, body) in ← moduleEntries env i do
          if keySet.contains (kind, key) then
            let canon := canonicalize body
            m := m.insert (kind, key) (canon, maskPositions key canon)
        return m
    let refBodies ← entriesOf refEnv refIdx
    let newBodies ← entriesOf newEnv newIdx
    let mod := refEnv.header.moduleNames[refIdx]!
    let mut r := reports.getD mod {}
    for (kind, key) in keys do
      let what := s!"{kind} {key}"
      let (c, m) := refBodies.getD (kind, key) ("", "")
      let (c', m') := newBodies.getD (kind, key) ("", "")
      r := if c == c' then r.push "equivalent body" what
        else if m == m' then r.push "source positions changed" what
        else r.push "body changed" what
    reports := reports.insert mod r
  let mut errors := allowErrors
  let mut totals : Report := {}
  for (mod, r) in reports.toArray.qsort (·.1.toString < ·.1.toString) do
    errors := errors + r.errors
    totals := { totals with added := totals.added + r.added }
    for c in categories do
      totals := { totals with diffs := totals.diffs.insert c (totals.diffs.getD c #[] ++ r.diffs.getD c #[]) }
    if r.diffs.isEmpty then continue
    IO.println s!"{mod}: {r.summary}"
    for c in categories do
      if c == "equivalent body" then continue
      for x in (r.diffs.getD c #[]).qsort (· < ·) do
        IO.println s!"  {c}: {x}"
  for n in allow do
    unless usedAllow.contains n do
      IO.println s!"note: allowlisted declaration {n} has no body change"
  IO.println s!"total: {totals.summary}"
  return errors

unsafe def showEntry (root : System.FilePath) (canon : Bool) (kind key : String) (mods : List String) : IO Unit := do
  let env ← importAll root mods
  runCore env do
    for h : i in [0:env.header.moduleNames.size] do
      for (k, n, sig, body) in ← moduleEntries env i do
        if k == kind && n == key then
          IO.println s!"-- {env.header.moduleNames[i]} {k} {n}\n-- sig: {sig}\n{if canon then canonicalize body else body}"

/-- Prints the keys of the entries of kind `kind` of module `mod`. -/
unsafe def listEntries (root : System.FilePath) (kind mod : String) : IO Unit := do
  let env ← importAll root [mod]
  let some i := env.header.moduleNames.idxOf? mod.toName | throw <| IO.userError s!"unknown module {mod}"
  runCore env do
    for (k, n, _, _) in ← moduleEntries env i do
      if k == kind then IO.println n

end CompilerABI

unsafe def main : List String → IO UInt32
  | "check" :: refRoot :: newRoot :: allow :: mods => do
    let errors ← CompilerABI.check refRoot newRoot allow mods
    return if errors == 0 then 0 else 1
  | "show" :: root :: kind :: key :: mods => do
    CompilerABI.showEntry root false kind key mods; return 0
  | "show-canonical" :: root :: kind :: key :: mods => do
    CompilerABI.showEntry root true kind key mods; return 0
  | ["list", root, kind, mod] => do
    CompilerABI.listEntries root kind mod; return 0
  | _ => do
    IO.eprintln "usage: compilerABI check <ref olean dir> <new olean dir> <allowlist> <module>..."
    IO.eprintln "       compilerABI (show | show-canonical) <olean dir> <kind> <key> <module>..."
    IO.eprintln "       compilerABI list <olean dir> <kind> <module>"
    return 2
