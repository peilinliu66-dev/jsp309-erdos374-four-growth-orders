/-
JSP309 engineering launcher prototype for the pinned Lean/Lake 4.30.0.
This adapts only the compiler executable of one exact original module.
The saved built-in leanArts facet still owns dependency, output and trace work.
No mathematical declarations or Lake build traces are supplied by this file.
-/
import Lake
import Lake.Load.Workspace
import Lake.Build.Module
import Lake.Build.Run
import Lake.CLI.Build
import Lake.CLI.Main

open System Lean Lake

namespace LakeFrontend309

structure FileBinding where
  path : String
  sha256 : String
  deriving FromJson, ToJson

structure Request where
  sysroot : String
  expectedLeanGithash : String
  workspace : String
  configFile : String := "lakefile.toml"
  heavyModule : String
  heavyPackage : String
  heavyLibrary : String
  heavySource : FileBinding
  dispatcher : String
  bridgePolicy : FileBinding
  dispatcherConfig : FileBinding
  python : String
  hashHelper : String
  adaptationFiles : Array FileBinding
  targets : Array String
  deriving FromJson

def sha256File (request : Request) (path : String) : IO String := do
  let out ← IO.Process.output {
    cmd := request.python
    args := #["-I", "-B", request.hashHelper, path]
  }
  unless out.exitCode == 0 && out.stderr.isEmpty do
    throw <| IO.userError s!"SHA256 helper failed for {path}: {out.stderr}"
  let digest := out.stdout.trimAscii.copy
  unless digest.length == 64 && digest.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
    throw <| IO.userError s!"invalid SHA256 helper response for {path}"
  return digest

def checkBinding (request : Request) (binding : FileBinding) : IO Unit := do
  unless (← sha256File request binding.path) == binding.sha256 do
    throw <| IO.userError s!"file bytes differ from binding: {binding.path}"

def sameExistingPath (a b : FilePath) : IO Bool := do
  let a ← IO.FS.realPath a
  let b ← IO.FS.realPath b
  return a.toString.toLower == b.toString.toLower

def checkRuntimePolicies (request : Request) : IO Unit := do
  for binding in #[request.bridgePolicy, request.dispatcherConfig] do
    checkBinding request binding
    unless request.adaptationFiles.any (fun file => file.path == binding.path && file.sha256 == binding.sha256) do
      throw <| IO.userError "runtime policy is absent from the strong compiler adaptation trace"
  let some policyPath ← IO.getEnv "LAKEFRONT309_BRIDGE_POLICY"
    | throw <| IO.userError "missing exact bridge policy environment"
  let some policySha ← IO.getEnv "LAKEFRONT309_BRIDGE_POLICY_SHA256"
    | throw <| IO.userError "missing exact bridge policy SHA256 environment"
  let some configPath ← IO.getEnv "LAKEFRONT309_CONFIG"
    | throw <| IO.userError "missing exact dispatcher config environment"
  unless (← sameExistingPath ⟨policyPath⟩ ⟨request.bridgePolicy.path⟩) &&
      policySha == request.bridgePolicy.sha256 &&
      (← sameExistingPath ⟨configPath⟩ ⟨request.dispatcherConfig.path⟩) do
    throw <| IO.userError "runtime bridge/dispatcher environment differs from frozen request"

def makeAdaptedConfig
  (request : Request) (originalWs : Workspace) (adaptationIdentity : String)
: ModuleFacetConfig Module.leanArtsFacet :=
  let stock := Module.leanArtsFacetConfig
  mkFacetJobConfig fun mod => do
    let ctx ← getBuildContext
    let originalTrace := BuildTrace.ofHash (pureHash originalWs.lakeEnv.leanGithash)
      s!"Lean {Lean.versionStringCore}, commit {originalWs.lakeEnv.leanGithash}"
    let exactName := mod.name.toString == request.heavyModule
    let exactOwner := mod.pkg.origName.toString == request.heavyPackage &&
      mod.lib.name.toString == request.heavyLibrary
    if exactName && !exactOwner then
      error s!"heavy module owner differs from request: {mod.name}"
    let heavy := exactName && exactOwner
    if heavy then
      unless (← sameExistingPath mod.leanFile ⟨request.heavySource.path⟩) do
        error "heavy source path differs from exact request"
      checkBinding request request.heavySource
    -- Retain the adapted facet map inherited from the running workspace.
    -- Restoring originalWs wholesale would bypass this dispatch in imports.
    let inheritedWs := ctx.workspace
    let selectedWs := if heavy then
      { inheritedWs with lakeEnv :=
        { originalWs.lakeEnv with lean :=
          { originalWs.lakeEnv.lean with lean := ⟨request.dispatcher⟩ } } }
      else { inheritedWs with lakeEnv := originalWs.lakeEnv }
    let selectedTrace := if heavy then
      originalTrace.mix <| .ofHash (pureHash adaptationIdentity)
        s!"JSP309 compiler adaptation SHA256 bindings: {adaptationIdentity}"
      else originalTrace
    let selectedContext := { ctx with opaqueWs := selectedWs, leanTrace := selectedTrace }
    withTheReader BuildContext (fun _ => selectedContext) <| stock.run mod

def execute (request : Request) : IO Unit := do
  unless Lean.versionStringCore == "4.30.0" do
    throw <| IO.userError s!"launcher compiled with unexpected Lean {Lean.versionStringCore}"
  if request.adaptationFiles.isEmpty || request.targets.isEmpty then
    throw <| IO.userError "adaptation files and targets must be nonempty"
  for binding in request.adaptationFiles do
    checkBinding request binding
  checkRuntimePolicies request
  checkBinding request request.heavySource
  let adaptationIdentity := (toJson request.adaptationFiles).compress
  let lean ← LeanInstall.get ⟨request.sysroot⟩
  unless lean.githash == request.expectedLeanGithash do
    throw <| IO.userError s!"original Lean commit differs: {lean.githash}"
  let options : LakeOptions := {
    rootDir := ⟨request.workspace⟩
    configFile := ⟨request.configFile⟩
    leanInstall? := some lean
    lakeInstall? := some (LakeInstall.ofLean lean)
    elanInstall? := ← findElanInstall?
    noCache := some true
    updateDeps := false
    updateToolchain := false
  }
  let loadConfig ← (options.mkLoadConfig).toIO (fun e => IO.userError (toString e))
  let some loaded ← (loadWorkspace loadConfig).toBaseIO {
    out := .stderr, outLv := .info, ansiMode := .noAnsi
  } | throw <| IO.userError "original workspace loading failed"
  let originalWs := { loaded with lakeEnv := { loaded.lakeEnv with enableArtifactCache? := some false } }
  let adapted := makeAdaptedConfig request originalWs adaptationIdentity
  let ws := originalWs.addModuleFacetConfig adapted
  let specs ← (parseTargetSpecs ws request.targets.toList).toIO (fun e => IO.userError (toString e))
  for spec in specs do
    unless spec.buildable do
      throw <| IO.userError "requested target is not buildable by the stock Lake build contract"
  let cfg : BuildConfig := {
    verbosity := .normal
    out := .stderr
    outLv := .info
    failLv := .warning
    ansiMode := .noAnsi
    showSuccess := true
  }
  ws.runBuild (buildSpecs specs) cfg
  for binding in request.adaptationFiles do
    checkBinding request binding
  checkRuntimePolicies request
  checkBinding request request.heavySource

end LakeFrontend309

def main (args : List String) : IO UInt32 := do
  try
    let [requestPath] := args
      | throw <| IO.userError "usage: LakeFrontend309 REQUEST.json"
    let raw ← IO.FS.readFile ⟨requestPath⟩
    let request : LakeFrontend309.Request ←
      match Json.parse raw >>= fromJson? with
      | .ok value => pure value
      | .error message => throw <| IO.userError s!"invalid request JSON: {message}"
    LakeFrontend309.execute request
    return (0 : UInt32)
  catch error =>
    IO.eprintln s!"LakeFrontend309 failed: {error}"
    return (1 : UInt32)
