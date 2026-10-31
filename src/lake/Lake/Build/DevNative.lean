/-
Copyright (c) 2026 Kevaundray Wedderburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevaundray Wedderburn
-/
module

prelude
public import Lake.Build.Job.Monad
public import Lake.Build.Infos
public import Lake.Config.Dynlib
import Lake.Build.Job.Register
import Lake.Build.Common
import Lake.Config.Workspace
import Lake.Config.LeanLib
import Lake.Config.ExternLib
import Lake.Util.StoreInsts
import Init.Data.String
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Native code of dependencies in development mode

With `LEAN_DEV_NATIVE=1` (opt-in, e.g. `LEAN_DEV_NATIVE=1 fast-lean build`), the modules of the
workspace's root package are elaborated with the compiled code of the dependency modules they
import loaded (`--load-dynlib`), so that tactics and other metaprograms of dependencies run
natively instead of in the interpreter. The libraries are not part of any trace and do not change
any output.

The dependency modules are those imported by the root package's libraries. Their C files, as
produced by Lake (or downloaded with their `.olean` files), are compiled into one shared library
per package and cached in `$XDG_CACHE_HOME/fast-lean/native` (default `~/.cache`), keyed by the
toolchain and the C files. A library is only linked if all its symbols resolve against the
toolchain and the libraries of its dependencies; otherwise, the package (and its dependents) fall
back to the interpreter with a notice.
-/

open System Lean

namespace Lake

/-- Whether `LEAN_DEV_NATIVE=1` asks for native dependency libraries (on Linux only). -/
def devNativeEnabled : BaseIO Bool := do
  return Platform.isLinux && (← IO.getEnv "LEAN_DEV_NATIVE") == some "1"

/-- The root directory of the native library cache. -/
def devNativeCacheDir? : BaseIO (Option FilePath) := do
  if let some dir ← IO.getEnv "XDG_CACHE_HOME" then
    if !dir.isEmpty then
      return some <| FilePath.mk dir / "fast-lean" / "native"
  return (← IO.getEnv "HOME").map (FilePath.mk · / ".cache" / "fast-lean" / "native")

/-- Replaces characters that are unsafe in file names. -/
def devNativeFileName (s : String) : String :=
  s.map fun c => if c.isAlphanum || c == '-' || c == '.' || c == '_' then c else '_'

/--
Identifies the toolchain build whose symbols native code links against (its shared libraries and
`lean.h`).
-/
def devNativeToolchainHash (lean : LeanInstall) (lake : LakeInstall) : IO Hash := do
  let mut h := Hash.ofString lean.sysroot.toString |>.mix (.ofString lean.githash)
  for lib in lean.sharedDynlibs.push lake.sharedDynlib do
    let md ← lib.path.metadata
    h := h.mix <| .ofString s!"{lib.path}:{md.byteSize}:{md.modified.sec}.{md.modified.nsec}"
  return h.mix (← computeBinFileHash (lean.includeDir / "lean" / "lean.h"))

/--
Returns `X` if `line` is `X = _init_X();`, i.e., the eager initialization of the constant `X`.
-/
def devNativeInitOf? (line : String) : Option String := do
  let [name, rhs] := line.splitOn " = _init_" | none
  guard (rhs == name ++ "();")
  return name

/--
Works around C files from toolchains (e.g., the official v4.34.0) that initialize the auxiliary
`_boxed_const` constants of `meta` code only in `runtime_initialize_*`, which regular imports do not
run: adds their initialization to `meta_initialize_*` (unless present) in declaration order. Unlike
the fixed compiler, this cannot tell which of them `meta` code uses, and so adds all of them.
Returns `none` if nothing is to be patched.
-/
def devNativePatchBoxedConsts (src : String) : Option String := do
  guard (src.contains "___boxed__const__" && src.contains "meta_initialize_")
  let lines := src.splitOn "\n" |>.toArray
  let bodyOf (prefix_ : String) : Option (Nat × Nat) := do
    let start ← lines.findIdx? (·.startsWith prefix_)
    let stop ← (lines.extract start).findIdx? (· == "return lean_io_result_mk_ok(lean_box(0));")
    return (start, start + stop)
  let (rtStart, rtStop) ← bodyOf "LEAN_EXPORT lean_object* runtime_initialize_"
  let (metaStart, metaStop) ← bodyOf "LEAN_EXPORT lean_object* meta_initialize_"
  -- definition order of the initializers, which is the declaration order
  let mut defIdx : Std.HashMap String Nat := {}
  for h : i in [0:lines.size] do
    let line := lines[i]
    if line.startsWith "static " && line.endsWith "(void){" then
      if let [_, name] := line.splitOn " _init_" then
        defIdx := defIdx.insert (name.dropEnd "(void){".length).copy i
  let mut metaInits : Array (String × Nat) := #[]
  for i in [metaStart:metaStop] do
    if let some name := devNativeInitOf? lines[i]! then
      metaInits := metaInits.push (name, i)
  -- statements to insert before the given line of `meta_initialize_*`
  let mut inserts : Std.HashMap Nat (Array String) := {}
  for i in [rtStart:rtStop] do
    let some name := devNativeInitOf? lines[i]! | continue
    unless name.contains "___boxed__const__" && !metaInits.any (·.1 == name) do continue
    let idx := defIdx.getD name 0
    let at_ := metaInits.find? (fun (n, _) => defIdx.getD n 0 > idx) |>.map (·.2) |>.getD metaStop
    let persist := lines[i+1]?.filter (· == s!"lean_mark_persistent({name});") |>.toArray
    inserts := inserts.alter at_ fun s? => some (s?.getD #[] |>.push lines[i]! |>.append persist)
  guard !inserts.isEmpty
  let mut out : Array String := #[]
  for h : i in [0:lines.size] do
    if let some stmts := inserts[i]? then
      out := out ++ stmts
    out := out.push lines[i]
  return "\n".intercalate out.toList

/-- Runs a process, returning its error output on failure (instead of logging it). -/
def devNativeRun (cmd : String) (args : Array String) : BaseIO (Except String Unit) := do
  match ← (IO.Process.output {cmd, args}).toBaseIO with
  | .ok out =>
    if out.exitCode == 0 then return .ok ()
    else if out.stderr.trimAscii.isEmpty then return .error s!"{cmd} exited with code {out.exitCode}"
    else return .error out.stderr
  | .error e => return .error s!"failed to run {cmd}: {e}"

/-- Configuration shared by the native builds of a workspace. -/
structure DevNativeConfig where
  lean : LeanInstall
  /-- Directory of this toolchain's objects and libraries. -/
  dir : FilePath
  toolchainHash : Hash

/--
A unique temporary file name next to `file`, which is then renamed to `file` so that concurrent
builds see either no file or a complete one.
-/
def devNativeTmp (file : FilePath) : BaseIO FilePath := do
  return file.toString ++ s!".tmp{← IO.Process.getPID}.{← IO.monoNanosNow}"

/-- Compiles the module's C file into the object cache. -/
def Module.fetchDevNativeObj (mod : Module) (cfg : DevNativeConfig) : FetchM (Job FilePath) := do
  let cJob ← mod.c.fetch
  withRegisterJob s!"{mod.name}:native" (optional := true) do
  cJob.mapM fun cFile => do
    let lean := cfg.lean
    let args := #["-I", (mod.leanIncludeDir?.getD lean.includeDir).toString] ++ lean.ccFlags ++
      mod.weakLeancArgs ++ mod.leancArgs ++ #["-DLEAN_EXPORTING"]
    let key := cfg.toolchainHash.mix cJob.getTrace.hash |>.mix (.ofString (" ".intercalate args.toList))
    let oFile := cfg.dir / "obj" / s!"{key.hex}.o"
    if (← oFile.pathExists) then
      return oFile
    updateAction .build
    IO.FS.createDirAll oFile.parent.get!
    let tmp ← devNativeTmp oFile
    let src ← id do
      let some patched := devNativePatchBoxedConsts (← IO.FS.readFile cFile) | pure cFile
      let src := tmp.addExtension "c"
      IO.FS.writeFile src patched
      pure src
    let res ← devNativeRun lean.cc.toString (#["-c", "-o", tmp.toString, src.toString] ++ args)
    if src != cFile then IO.FS.removeFile src
    match res with
    | .ok () => IO.FS.rename tmp oFile; return oFile
    | .error e => removeFileIfExists tmp; error e

/-- The first line of linker output naming an undefined symbol, or else its first line. -/
def devNativeLinkReason (err : String) : String :=
  let lines := err.splitOn "\n" |>.map (·.trimAscii.copy) |>.filter (!·.isEmpty)
  let undefined? := lines.find? fun l => l.contains "undefined symbol" || l.contains "undefined reference"
  undefined?.getD (lines.head?.getD err)

/--
Links `libFile` unless it exists, returning whether it did so. The failure reason is recorded, so
that a library that cannot be linked is not attempted again.
-/
def devNativeLink (cc : FilePath) (libFile : FilePath) (linkArgs : Array String) :
    IO (Except String Bool) := do
  let failedFile := libFile.withFileName "failed"
  if (← libFile.pathExists) then
    return .ok false
  if (← failedFile.pathExists) then
    return .error (← IO.FS.readFile failedFile).trimAscii.copy
  IO.FS.createDirAll libFile.parent.get!
  let tmp ← devNativeTmp libFile
  let rsp := tmp.addExtension "rsp"
  let quote (arg : String) := "\"" ++ (arg.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""
  IO.FS.writeFile rsp ("\n".intercalate (linkArgs.map quote).toList)
  let res ← devNativeRun cc.toString #["-shared", "-o", tmp.toString, s!"@{rsp}"]
  IO.FS.removeFile rsp
  match res with
  | .ok () =>
    IO.FS.rename tmp libFile
    return .ok true
  | .error e =>
    if (← tmp.pathExists) then IO.FS.removeFile tmp
    let reason := devNativeLinkReason e
    IO.FS.writeFile failedFile reason
    return .error reason

/--
Links the native library of a package from the objects of its modules, verifying that all its
symbols resolve against the toolchain and the libraries of its dependencies. Never fails: an
unavailable library is `none`, with a notice.
-/
def devNativeLinkLib
  (pkg : Package) (objsJob : Job (Array FilePath)) (depsJob : Job (Array (Option Dynlib)))
  (cfg : DevNativeConfig)
: FetchM (Job (Option Dynlib)) :=
  withRegisterJob s!"{pkg.prettyName}:native" do
  let inputs := objsJob.zipResultWith (other := depsJob) fun r1 r2 =>
    .ok (r1.result?, r2.result?) {}
  inputs.mapM fun (objs?, deps?) => do
    let unavailable (reason : String) := do
      logInfo s!"native code of '{pkg.prettyName}' is unavailable, using the interpreter: {reason}"
      return none
    let some objs := objs? | unavailable "some of its modules could not be compiled"
    let some deps := deps?.bind (·.mapM id) | unavailable "a dependency is unavailable"
    let lean := cfg.lean
    let name := s!"native_{devNativeFileName pkg.prettyName}"
    let linkArgs := objs.map (·.toString) ++ #["-Wl,--as-needed"] ++ deps.map (·.path.toString) ++
      #["-L", lean.leanLibDir.toString, "-lleanshared", "-lleanshared_1", "-lleanshared_2",
        "-lInit_shared", "-lLake_shared", s!"-Wl,-rpath,{lean.leanLibDir}", "-Wl,--no-undefined"] ++
      lean.ccLinkSharedFlags
    let key := cfg.toolchainHash.mix (.ofString (" ".intercalate linkArgs.toList))
    let libFile := cfg.dir / key.hex / s!"lib{name}.so"
    match ← (devNativeLink lean.cc libFile linkArgs).toBaseIO with
    | .ok (.ok built) =>
      if built then updateAction .build
      return some {name, path := libFile, deps}
    | .ok (.error reason) => unavailable reason
    | .error e => unavailable (toString e)

/-- Orders packages such that dependencies come before their dependents. -/
partial def devNativePackageOrder (ws : Workspace) : Array Package :=
  let rec visit (pkg : Package) (acc : Array Package × Std.HashSet Nat) :=
    let (order, seen) := acc
    if seen.contains pkg.wsIdx then acc else
    let acc := pkg.depIdxs.foldl (init := (order, seen.insert pkg.wsIdx)) fun acc i =>
      if h : i < ws.packages.size then visit ws.packages[i] acc else acc
    (acc.1.push pkg, acc.2)
  (visit ws.root (#[], {})).1

/--
Builds the native libraries of the dependency modules imported by the root package's libraries
(skipping modules whose imports cannot be determined, which fail to build anyway).

Like Lake's import graph processing, this fetches and awaits on the current thread, so that other
fetches of the same targets do not race with it.
-/
def fetchDevNativeLibsCore (cfg : DevNativeConfig) : FetchM (Job (Array Dynlib)) := do
  let ws ← getWorkspace
  let mut modsOf : Std.HashMap Nat (Array Module) := {}
  let mut seen : Std.HashSet Name := {}
  for lib in ws.root.leanLibs do
    let some mods ← (← lib.modules.fetch).wait? | continue
    for mod in mods do
      let some imps ← (← mod.transImports.fetch).wait? | continue
      for imp in imps do
        unless imp.pkg.isRoot || seen.contains imp.name do
          seen := seen.insert imp.name
          modsOf := modsOf.alter imp.pkg.wsIdx fun mods? => some (mods?.getD #[] |>.push imp)
  let order := devNativePackageOrder ws
  let mut transDeps : Std.HashMap Nat (Std.HashSet Nat) := {}
  for pkg in order do
    let mut deps : Std.HashSet Nat := {}
    for i in pkg.depIdxs do
      deps := deps.insert i
      for j in transDeps.getD i {} do
        deps := deps.insert j
    transDeps := transDeps.insert pkg.wsIdx deps
  let mut libs : Std.HashMap Nat (Job (Option Dynlib)) := {}
  -- packages with other native code are left to Lake (and thus their dependents are, too)
  let mut excluded : Std.HashSet Nat := {}
  for pkg in order do
    let some mods := modsOf[pkg.wsIdx]? | continue
    let deps := transDeps.getD pkg.wsIdx {}
    if !pkg.externLibs.isEmpty || mods.any (·.shouldPrecompile) || deps.any excluded.contains then
      excluded := excluded.insert pkg.wsIdx
      continue
    let objJobs ← mods.mapM (·.fetchDevNativeObj cfg)
    let depJobs := order.filterMap fun p => if deps.contains p.wsIdx then libs[p.wsIdx]? else none
    let lib ← devNativeLinkLib pkg (Job.collectArray objJobs) (Job.collectArray depJobs) cfg
    libs := libs.insert pkg.wsIdx lib
  let libJobs := order.filterMap (libs[·.wsIdx]?)
  return (Job.collectArray libJobs).map (·.filterMap id)

/-- The native libraries of a workspace's dependencies, built once per build. -/
package_data devNative : Array Dynlib

theorem devNative_job_eq (t : BuildKey) :
    Job (Array Dynlib) = Job (BuildData (.facet t (Package.facetKind ++ `devNative))) := by
  show _ = Job (FacetOut _); rw [FamilyOut.fam_eq (f := FacetOut) (a := Package.facetKind ++ `devNative)]

/--
The native libraries to load when elaborating the modules of the root package (in load order), if
enabled by `LEAN_DEV_NATIVE=1`.
-/
def fetchDevNativeLibs? : FetchM (Option (Job (Array Dynlib))) := do
  unless (← devNativeEnabled) do return none
  let some cacheDir ← devNativeCacheDir? | return none
  let t := BuildKey.package (← getWorkspace).root.keyName
  let key := BuildKey.facet t (Package.facetKind ++ `devNative)
  -- modules are set up concurrently, so the first one claims the build atomically
  let promise ← IO.Promise.new
  let claimed : Job (Array Dynlib) := .ofTask (promise.result?.map (·.getD (.ok #[] {})))
  let job? ← modifyGetThe BuildStore fun store =>
    match store.get? key with
    | some job => (some job, store)
    | none => (none, store.insert key (cast (devNative_job_eq t) claimed))
  if let some job := job? then
    return some (cast (devNative_job_eq t).symm job)
  let job ← withRegisterJob "native dependencies" do
    let unavailable (reason : String) : Job (Array Dynlib) :=
      .pure #[] (log := ({} : Log).push <| .info
        s!"native code of the dependencies is unavailable, using the interpreter: {reason}")
    let lean ← getLeanInstall
    let lake ← getLakeInstall
    let toolchain := (← getLakeEnv).toolchain
    let toolchain := if toolchain.isEmpty then s!"lean-{lean.githash}" else toolchain
    let toolchain := toolchain.replace "/" "--" |>.replace ":" "---"
    let .ok toolchainHash ← (devNativeToolchainHash lean lake).toBaseIO
      | return unavailable "could not identify the toolchain"
    let cfg := {lean, dir := cacheDir / devNativeFileName toolchain, toolchainHash}
    fetchDevNativeLibsCore cfg
  discard <| BaseIO.mapTask (t := job.task) (promise.resolve ·)
  return some claimed

/-- Adds the native libraries of the dependencies to the module's setup, without tracing them. -/
public def Module.withDevNativeLibs (mod : Module) (job : Job ModulePreSetup) :
    FetchM (Job ModulePreSetup) := do
  unless mod.pkg.isRoot do return job
  let some libsJob ← fetchDevNativeLibs? | return job
  return job.zipWith (other := libsJob) fun presetup libs =>
    {presetup with dynlibs := libs ++ presetup.dynlibs}

end Lake
