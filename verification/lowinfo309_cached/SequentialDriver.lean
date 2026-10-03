/-
Engineering prototype for Lean 4.30.0. This file is not a proof certificate.
Independent cached-export variant; the frozen original driver is unchanged.
It calls the stock parser, command elaborator, linters and kernel insertion APIs.
No theorem source is rewritten and no declaration is supplied by this driver.
-/
module

import Lean.Elab.Frontend
import Lean.Compiler.LCNF.EmitC
import Lean.Compiler.Options
import Lean.Util.Path
import Lean.Util.CollectAxioms
-- Access the stock metadata cache for an explicit reset at final EOF.
-- No private collector implementation or mathematical declaration is copied.
import all Lean.LibrarySuggestions.SymbolFrequency

open Lean Lean.Elab Lean.Elab.Frontend

namespace LowInfo309

structure Request where
  source : String
  setup : String
  sysroot : String
  olean : String
  ilean : Option String := none
  cFile : Option String := none
  report : String
  cmdlineOptions : LeanOptions := {}
  cliPlugins : Array System.FilePath := #[]
  infoEnabled : Bool := true
  failOnWarnings : Bool := false
  expectedNames : Array Name := #[]
  -- Default preserves the original direct public collectAxioms path.
  postExportCachedAxioms : Bool := false
  provisionalOlean : Option String := none
  -- Exact source SHA256 is verified by the external frozen manifest/dispatcher.
  -- This driver checks request path identity and unchanged bytes, not a host path.
  expectedHeavySource : Option String := none
  prewarmSymbolFrequency : Bool := false
  metadataMaxHeartbeats : Nat := 20000000
  deriving FromJson

-- Derived FromJson does not apply constructor default values for missing Bool/Nat
-- fields. Preserve the original request schema while defaulting only new controls.
def requestFromJson (input : Json) : Except String Request := do
  discard <| input.getObj?
  let mut value := input
  for (key, fallback) in
      [("postExportCachedAxioms", toJson false), ("provisionalOlean", Json.null)
       , ("expectedHeavySource", Json.null), ("prewarmSymbolFrequency", toJson false)
       , ("metadataMaxHeartbeats", toJson (20000000 : Nat))] do
    if let .error _ := value.getObjVal? key then
      value := value.setObjVal! key fallback
  fromJson? value

structure Counts where
  commands : Nat := 0
  errors : Nat := 0
  warnings : Nat := 0
  deriving ToJson

def Counts.add (a b : Counts) : Counts :=
  { commands := a.commands + b.commands
    errors := a.errors + b.errors
    warnings := a.warnings + b.warnings }

def reportLog (log : MessageLog) : IO Counts := do
  let mut counts : Counts := {}
  -- Inspect even reported/silent diagnostics. Failures cannot disappear with a reset.
  for msg in log.reportedPlusUnreported do
    let j ← msg.toJson
    IO.println j.compress
    match msg.severity with
    | .error => counts := { counts with errors := counts.errors + 1 }
    | .warning => counts := { counts with warnings := counts.warnings + 1 }
    | .information => pure ()
  (← IO.getStdout).flush
  return counts

def assertOptions (opts : Options) : IO Unit := do
  if debug.skipKernelTC.get opts then
    throw <| IO.userError "refusing debug.skipKernelTC=true"
  if Elab.async.get opts then
    throw <| IO.userError "this prototype requires Elab.async=false"
  if Elab.inServer.get opts then
    throw <| IO.userError "this prototype requires command-line mode, Elab.inServer=false"
  if Compiler.compiler.postponeCompile.get opts then
    throw <| IO.userError "this prototype requires compiler.postponeCompile=false"

def assertState (st : Command.State) (moduleName : Name) (infoEnabled : Bool) : IO Unit := do
  if st.env.header.trustLevel != 0 then
    throw <| IO.userError "refusing a nonzero kernel trust level"
  if st.env.header.mainModule != moduleName then
    throw <| IO.userError "main module name changed"
  if st.infoState.enabled != infoEnabled then
    throw <| IO.userError "InfoState.enabled changed inside source elaboration"
  for scope in st.scopes do
    assertOptions scope.opts

def mergeRefInfo (a b : Lsp.RefInfo) : Lsp.RefInfo := Id.run do
  -- Stock findModuleRefs deduplicates by identifier and source range across
  -- all command trees. Section-variable contexts can repeat an earlier range.
  let mut usages : Array Lsp.RefInfo.Location := #[]
  for usage in a.usages ++ b.usages do
    unless usages.any (fun old => old.range == usage.range) do
      usages := usages.push usage
  return { definition? := a.definition?.orElse fun _ => b.definition?
           usages := usages.qsort (fun x y => x.range < y.range) }

def mergeRefs (a b : Lsp.ModuleRefs) : Lsp.ModuleRefs :=
  b.foldl (init := a) fun acc ident info =>
    acc.insert ident <| mergeRefInfo (acc.getD ident Lsp.RefInfo.empty) info

structure SlimRefs where
  refs : Lsp.ModuleRefs := ∅
  decls : Lsp.Decls := ∅

def collectSlimRefs (inputCtx : Parser.InputContext) (infoState : InfoState) : IO SlimRefs := do
  let task := infoState.substituteLazy
  let resolved := task.get
  let refs := Server.findModuleRefs inputCtx.fileMap resolved.trees.toArray (localVars := false)
  let (refs, decls) ← refs.toLspModuleRefs
  return { refs, decls }

structure LoopResult where
  counts : Counts := {}
  refs : SlimRefs := {}
  eof : Bool := false
  eofByte : Nat := 0

partial def loop (moduleName : Name) (infoEnabled : Bool) (acc : LoopResult) : FrontendM LoopResult := do
  let ictx ← getInputContext
  let before ← get
  liftM <| assertState before.commandState moduleName infoEnabled
  let scope := before.commandState.scopes.head!
  let pmctx : Parser.ParserModuleContext :=
    { env := before.commandState.env, options := scope.opts
      currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  let (stx, ps, parserMessages) :=
    Parser.parseCommand ictx pmctx before.parserState .empty
  let parsedCounts ← liftM <| reportLog parserMessages
  modify fun s =>
    { s with
      parserState := ps
      cmdPos := before.parserState.pos
      commands := #[]
      commandState := { s.commandState with messages := {}, traceState := {}, snapshotTasks := #[] } }
  -- The real stock top-level entry runs the normal registered command linters.
  elabCommandAtFrontend stx
  let after ← get
  liftM <| assertState after.commandState moduleName infoEnabled
  let commandCounts ← liftM <| reportLog after.commandState.messages
  -- async=false is not assumed to imply no tasks from custom elaborators.
  -- Drain the complete current-command DAG before releasing its references.
  let taskTree : Language.SnapshotTree :=
    .mk { diagnostics := .empty } after.commandState.snapshotTasks
  let taskCounts ← liftM <| taskTree.foldM
    (fun counts snap => Counts.add counts <$> reportLog snap.diagnostics.msgLog) ({} : Counts)
  let slim ← if infoEnabled then
      liftM <| collectSlimRefs ictx after.commandState.infoState
    else pure ({} : SlimRefs)
  let counts := acc.counts.add parsedCounts |>.add commandCounts |>.add taskCounts
  let counts := { counts with commands := counts.commands + 1 }
  let acc := { acc with
    counts
    refs := { refs := mergeRefs acc.refs.refs slim.refs
              decls := acc.refs.decls.insertMany slim.decls } }
  liftM <| IO.println <| Json.compress <| Json.mkObj
    [("prototype_event", toJson "command_complete"), ("command_index", toJson counts.commands)
     , ("syntax_kind", toJson stx.getKind), ("end_byte", toJson ps.pos.byteIdx)
     , ("trust_level", toJson (0 : Nat)), ("check_kernel", toJson true)]
  liftM <| (← IO.getStdout).flush
  -- Only the live environment/scopes/parser state and pure serialized reference data survive.
  modify fun s =>
    { s with
      commands := #[]
      commandState := { s.commandState with
        messages := {}
        traceState := {}
        snapshotTasks := #[]
        infoState := { enabled := infoEnabled } } }
  if stx.isOfKind ``Lean.Parser.Command.eoi then
    unless ictx.atEnd ps.pos do
      throw <| IO.userError "eoi before actual end of source bytes"
    return { acc with eof := true, eofByte := ps.pos.byteIdx }
  if Parser.isTerminalCommand stx then
    throw <| IO.userError "refusing premature terminal command (#exit or misplaced import)"
  if ps.pos == before.parserState.pos then
    throw <| IO.userError "parser made no progress"
  loop moduleName infoEnabled acc

def localCheckedNames (env : Environment) : Array Name :=
  env.checked.get.constants.foldStage2 (fun names name _ => names.push name) #[]
    |>.qsort Name.lt

-- Lightweight signatures intentionally omit proof/definition values. Stock export
-- produces the provisional artifact directly from the fully checked environment.
-- Reimport equality below covers the saved signature/metadata, not proof-body equality.
structure LocalSignature where
  name : Name
  levelParams : List Name
  type : Expr
  kind : String
  isUnsafe : Bool
  isPartial : Bool
  hints : ReducibilityHints
  all : List Name
  payloadMetadata : String

structure LocalInventory where
  names : Array Name
  signatures : Array LocalSignature

def constantKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def quotKindName : QuotKind → String
  | .type => "type"
  | .ctor => "ctor"
  | .lift => "lift"
  | .ind => "ind"

-- Constructor-specific lightweight metadata includes all safety/recursion flags.
-- Recursor rule names/field counts are retained; RHS expressions and proof values
-- are deliberately not kept alive across the environment-release boundary.
def constantPayloadMetadata (info : ConstantInfo) : String :=
  let fields : List (String × Json) := match info with
    | .axiomInfo v => [("isUnsafe", toJson v.isUnsafe)]
    | .defnInfo v => [("safety", toJson (toString (repr v.safety)))]
    | .thmInfo _ => []
    | .opaqueInfo v => [("isUnsafe", toJson v.isUnsafe)]
    | .quotInfo v => [("kind", toJson (quotKindName v.kind))]
    | .inductInfo v =>
      [("numParams", toJson v.numParams), ("numIndices", toJson v.numIndices)
       , ("ctors", toJson v.ctors), ("numNested", toJson v.numNested)
       , ("isRec", toJson v.isRec), ("isUnsafe", toJson v.isUnsafe)
       , ("isReflexive", toJson v.isReflexive)]
    | .ctorInfo v =>
      [("induct", toJson v.induct), ("cidx", toJson v.cidx)
       , ("numParams", toJson v.numParams), ("numFields", toJson v.numFields)
       , ("isUnsafe", toJson v.isUnsafe)]
    | .recInfo v =>
      [("numParams", toJson v.numParams), ("numIndices", toJson v.numIndices)
       , ("numMotives", toJson v.numMotives), ("numMinors", toJson v.numMinors)
       , ("k", toJson v.k), ("isUnsafe", toJson v.isUnsafe)
       , ("rules", toJson (v.rules.map fun rule =>
           Json.mkObj [("ctor", toJson rule.ctor), ("nfields", toJson rule.nfields)]))]
  (Json.mkObj fields).compress

def signatureOf (info : ConstantInfo) : LocalSignature :=
  { name := info.name, levelParams := info.levelParams, type := info.type
    kind := constantKind info, isUnsafe := info.isUnsafe, isPartial := info.isPartial
    hints := info.hints, all := info.all, payloadMetadata := constantPayloadMetadata info }

-- Expr's BEq uses alpha-equivalence; strict Expr.equal preserves binder annotations.
def sameSignature (a b : LocalSignature) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && Expr.equal a.type b.type &&
    a.kind == b.kind && a.isUnsafe == b.isUnsafe && a.isPartial == b.isPartial &&
    a.hints == b.hints && a.all == b.all && a.payloadMetadata == b.payloadMetadata

-- Cheap guards cover the exact original Stage2 before any provisional export,
-- including private names and every generated auxiliary kernel declaration.
def inventoryLocals (env : Environment) (expected : Array Name) : IO LocalInventory := do
  let names := localCheckedNames env
  for required in expected do
    unless names.contains required do
      throw <| IO.userError s!"expected source declaration absent: {required}"
  let mut signatures : Array LocalSignature := #[]
  for name in names do
    let some info := env.checked.get.find? name
      | throw <| IO.userError s!"checked constant disappeared: {name}"
    if info.name != name then
      throw <| IO.userError s!"checked constant name mismatch: {name}"
    if info.isUnsafe then
      throw <| IO.userError s!"new unsafe declaration: {name}"
    if info matches .axiomInfo _ then
      throw <| IO.userError s!"new axiom declaration: {name}"
    signatures := signatures.push (signatureOf info)
  return { names, signatures }

def prototypeEvent (kind : String) (fields : List (String × Json) := []) : IO Unit := do
  IO.println <| Json.compress <| Json.mkObj (("prototype_event", toJson kind) :: fields)
  (← IO.getStdout).flush

def warmSymbolFrequency (env : Environment) (opts : Options) (budget : Nat) : IO Unit := do
  if budget <= 200000 then
    throw <| IO.userError "metadata warmup requires a finite budget above stock 200000"
  if env.header.trustLevel != 0 then
    throw <| IO.userError "metadata warmup requires kernel trust zero"
  assertOptions opts
  -- This global cache could have been populated by a suggestion during elaboration.
  -- Reset it only after complete EOF, then let the public stock query compute the
  -- actual final environment's map. Never install an empty or fabricated map.
  LibrarySuggestions.localSymbolFrequencyMapRef.set none
  let metadataOpts := maxHeartbeats.set opts budget
  assertOptions metadataOpts
  prototypeEvent "symbol_frequency_warmup_begin" [("max_heartbeats", toJson budget)]
  let (probe, metadataState) ← (withoutExporting (LibrarySuggestions.localSymbolFrequency .anonymous)).run' {} {}
    |>.toIO { fileName := "<stock-symbol-frequency-metadata>", fileMap := default,
               options := metadataOpts } { env }
  let metadataCounts ← reportLog metadataState.messages
  if metadataCounts.errors != 0 || metadataCounts.warnings != 0 then
    throw <| IO.userError "stock symbol-frequency metadata warmup emitted error/warning"
  unless (← LibrarySuggestions.localSymbolFrequencyMapRef.get).isSome do
    throw <| IO.userError "stock symbol frequency query did not populate its cache"
  prototypeEvent "symbol_frequency_warmup_complete"
    [("probe_frequency", toJson probe), ("max_heartbeats", toJson budget)
     , ("trust_level", toJson (0 : Nat)), ("skip_kernel_tc", toJson false)]

def exportWithMetadataBaseline (env : Environment) (path : System.FilePath)
    (writeIR : Bool) (resetBaseline : Bool) : IO Unit := do
  if env.header.trustLevel != 0 then
    throw <| IO.userError "metadata export requires kernel trust zero"
  if resetBaseline then
    let prior ← IO.getNumHeartbeats
    prototypeEvent "metadata_export_heartbeat_baseline_reset"
      [("prior_thread_heartbeats", toJson prior), ("kernel_checking_unchanged", toJson true)]
    -- Official unsafeRunMetaM creates initHeartbeats=0. Give metadata export its
    -- own finite stock 200000 budget by resetting this thread's counter here.
    -- Source elaboration/kernel insertion and all cheap guards have already ended.
    IO.setNumHeartbeats 0
    try
      writeModule (writeIR := writeIR) env path
    finally
      let metadataHeartbeats ← IO.getNumHeartbeats
      IO.setNumHeartbeats (prior + metadataHeartbeats)
  else
    writeModule (writeIR := writeIR) env path

def assertCachedHeavyTarget (request : Request) (env : Environment) : IO Unit := do
  if env.header.isModule then
    throw <| IO.userError "post-export cached audit is restricted to non-module source"
  if env.header.mainModule !=
      `RiemannZeta.GuthMaynard.HughesYoungActiveComplementSourceLine then
    throw <| IO.userError "post-export cached request is restricted to the exact heavy module"
  let source ← IO.FS.realPath ⟨request.source⟩
  let some expectedSource := request.expectedHeavySource
    | throw <| IO.userError "cached request requires the manifest-bound expectedHeavySource path"
  let heavy ← IO.FS.realPath ⟨expectedSource⟩
  let samePath := if System.Platform.isWindows then
      source.toString.toLower == heavy.toString.toLower
    else source.toString == heavy.toString
  unless samePath do
    throw <| IO.userError "post-export cached request source is not the exact heavy source"
  unless source.fileName == some "HughesYoungActiveComplementSourceLine.lean" do
    throw <| IO.userError "cached request source has a different heavy-source basename"

def checkProvisionalPath (request : Request) (path : System.FilePath) : IO Unit := do
  unless path.toString.endsWith ".provisional.olean" do
    throw <| IO.userError "provisional output must end in .provisional.olean"
  if ← path.pathExists then
    throw <| IO.userError "refusing an already existing provisional olean"
  for reserved in #[request.source, request.setup, request.olean, request.report] ++
      request.ilean.toArray ++ request.cFile.toArray do
    if path.normalize.toString.toLower ==
        (System.FilePath.mk reserved).normalize.toString.toLower then
      throw <| IO.userError "provisional output aliases a reserved request path"

def auditLocals (env : Environment) (expected : Array Name) : IO Json := do
  let names := localCheckedNames env
  for required in expected do
    unless names.contains required do
      throw <| IO.userError s!"expected source declaration absent: {required}"
  let mut entries : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name
      | throw <| IO.userError s!"checked constant disappeared: {name}"
    if info.isUnsafe then
      throw <| IO.userError s!"new unsafe declaration: {name}"
    if info matches .axiomInfo _ then
      throw <| IO.userError s!"new axiom declaration: {name}"
    let axes ← (collectAxioms name : CoreM (Array Name)).toIO'
      { fileName := "<prototype-axiom-audit>", fileMap := default } { env }
    for ax in axes do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throw <| IO.userError s!"unsupported axiom dependency of {name}: {ax}"
    entries := entries.push <| Json.mkObj [("name", toJson name), ("axioms", toJson axes)]
  return Json.mkObj [("count", toJson names.size), ("entries", toJson entries)]

structure PreparedSource where
  setup : ModuleSetup
  header : HeaderSyntax
  sourceBytes : ByteArray
  setupBytes : ByteArray
  result : LoopResult
  finalState : Frontend.State
  finalOpts : Options

def prepareSource (request : Request) : IO PreparedSource := do
  if request.ilean.isSome && !request.infoEnabled then
    throw <| IO.userError "cannot request a complete ilean with InfoState disabled"
  let sourceBytes ← IO.FS.readBinFile request.source
  let some source := String.fromUTF8? sourceBytes
    | throw <| IO.userError "source is not valid UTF-8; no lossy decoding is allowed"
  unless source.toUTF8 == sourceBytes do
    throw <| IO.userError "source UTF-8 round trip changed bytes"
  -- Boundary checks cannot intercept a local set_option ... in ... override.
  -- Refuse any mention before parsing; approved mathematical target has none.
  for forbidden in ["debug.skipKernelTC", "Elab.async", "Elab.inServer", "compiler.postponeCompile"] do
    if (source.splitOn forbidden).length != 1 then
      throw <| IO.userError s!"source contains protected option name {forbidden}"
  let setupBytes ← IO.FS.readBinFile request.setup
  let setup ← ModuleSetup.load request.setup
  initSearchPath ⟨request.sysroot⟩
  let inputCtx := Parser.mkInputContext source request.source
  let (header, parserState, parserMessages) ← Parser.parseHeader inputCtx
  let headerCounts ← reportLog parserMessages
  if headerCounts.errors != 0 then
    throw <| IO.userError "header parser errors; no output written"
  let opts := request.cmdlineOptions.toOptions
  let opts := internal.cmdlineSnapshots.setIfNotSet opts true
  let opts := Elab.async.setIfNotSet opts true
  setup.dynlibs.forM Lean.loadDynlib
  let opts := opts.mergeBy (fun _ _ hOpt => hOpt) setup.options.toOptions
  assertOptions opts
  let isModule := setup.isModule || HeaderSyntax.isModule header
  let imports := setup.imports?.getD (HeaderSyntax.imports header)
  let (env, importMessages) ← processHeaderCore (HeaderSyntax.startPos header) imports isModule opts .empty
    inputCtx (trustLevel := 0) (plugins := request.cliPlugins ++ setup.plugins)
    (leakEnv := true) (mainModule := setup.name) (package? := setup.package?) (arts := setup.importArts)
  let importCounts ← reportLog importMessages
  if importCounts.errors != 0 then
    throw <| IO.userError "import errors; no output written"
  let opts ← Language.Lean.reparseOptions opts
  assertOptions opts
  let commandState := { Command.mkState env {} opts with infoState := { enabled := request.infoEnabled } }
  assertState commandState setup.name request.infoEnabled
  let initial : Frontend.State := { commandState, parserState, cmdPos := parserState.pos }
  let initialResult : LoopResult := { counts := headerCounts.add importCounts }
  let (result, finalState) ← (loop setup.name request.infoEnabled initialResult).run { inputCtx } |>.run initial
  unless result.eof && result.eofByte == sourceBytes.size do
    throw <| IO.userError "complete source EOF was not reached"
  if result.counts.errors != 0 then
    throw <| IO.userError "parser/elaboration/kernel/task errors occurred; no output written"
  if request.failOnWarnings && result.counts.warnings != 0 then
    throw <| IO.userError "warnings rejected by strict prototype request; no output written"
  assertState finalState.commandState setup.name request.infoEnabled
  return { setup, header, sourceBytes, setupBytes, result, finalState
           finalOpts := finalState.commandState.scopes.head!.opts }

def bindInputs (request : Request) (sourceBytes setupBytes : ByteArray) : IO Unit := do
  unless (← IO.FS.readBinFile request.source) == sourceBytes do
    throw <| IO.userError "source bytes changed during compilation/audit"
  unless (← IO.FS.readBinFile request.setup) == setupBytes do
    throw <| IO.userError "setup bytes changed during compilation/audit"

def writeIlean (request : Request) (prepared : PreparedSource) (path : System.FilePath) : IO Unit := do
  unless request.infoEnabled do
    throw <| IO.userError "cannot write a complete ilean with InfoState disabled"
  let output : Server.Ilean := {
    module := prepared.setup.name
    directImports := Server.collectImports prepared.header
    references := prepared.result.refs.refs
    decls := prepared.result.refs.decls }
  IO.FS.writeFile path <| Json.compress <| toJson output

def emitSourceC (request : Request) (env : Environment) (moduleName : Name)
    (path : System.FilePath) : IO Unit := do
  let (data, compilerState) ← Compiler.LCNF.emitC moduleName
    |>.toIO { fileName := request.source, fileMap := default } { env }
  let compilerCounts ← reportLog compilerState.messages
  if compilerCounts.errors != 0 || compilerCounts.warnings != 0 then
    throw <| IO.userError "C emitter emitted error/warning"
  IO.FS.writeFile path data

def finalReport (request : Request) (moduleName : Name) (counts : Counts)
    (sourceBytes eofByte : Nat) (moduleSystem metadataWarmed : Bool)
    (declarationAudit : Json) : Json :=
  Json.mkObj
    [("status", toJson "prototype_completed_not_acceptance"), ("module", toJson moduleName)
     , ("source_bytes", toJson sourceBytes), ("eof_byte", toJson eofByte)
     , ("counts", toJson counts), ("trust_level", toJson (0 : Nat))
     , ("skip_kernel_tc", toJson false), ("check_kernel", toJson true)
     , ("info_enabled_per_command", toJson request.infoEnabled)
     , ("info_dependent_linters_have_inputs", toJson request.infoEnabled)
     , ("kernel_declarations", declarationAudit), ("module_system", toJson moduleSystem)
     , ("post_export_cached_axioms", toJson request.postExportCachedAxioms)
     , ("symbol_frequency_metadata_warmed", toJson metadataWarmed)
     , ("metadata_max_heartbeats", toJson request.metadataMaxHeartbeats)
     , ("metadata_export_heartbeat_baseline_reset",
         toJson (request.prewarmSymbolFrequency || request.postExportCachedAxioms))
     , ("ilean_semantic_equivalence_to_stock", toJson "not_yet_verified")]

def writeReport (request : Request) (report : Json) : IO Unit := do
  IO.FS.writeFile ⟨request.report⟩ report.pretty
  IO.println report.compress
  (← IO.getStdout).flush

-- The imported provisional file may remain mapped on Windows. Copy with bounded
-- memory to an unimported sibling, then rename that sibling into the final target.
-- Keep the genuine provisional file as evidence; never serialize the env again.
def publishProvisional (provisional target : System.FilePath) : IO Unit := do
  let pending := target.addExtension "publish-pending"
  if ← pending.pathExists then
    throw <| IO.userError "refusing an existing publication staging file"
  IO.FS.withFile provisional .read fun input =>
    IO.FS.withFile pending .write fun output => do
      let mut done := false
      while !done do
        let chunk ← input.read (1048576 : USize)
        if chunk.isEmpty then
          done := true
        else
          output.write chunk
      output.flush
  IO.FS.rename pending target

-- This product deliberately contains no Environment, Frontend/Command/Core State,
-- ConstantInfo, proof value, info tree, parser state or header syntax.
-- Returning stage1 drops its direct references to the giant local proof environment
-- before stage2 imports. Actual process memory still needs measurement; types remain.
structure StagedCachedProduct where
  moduleName : Name
  setup : ModuleSetup
  opts : Options
  inventory : LocalInventory
  sourceBytes : ByteArray
  setupBytes : ByteArray
  counts : Counts
  eofByte : Nat
  provisional : System.FilePath
  provisionalC : Option System.FilePath
  provisionalIlean : Option System.FilePath

def stagePreparedNonmodule (request : Request) (prepared : PreparedSource) : IO StagedCachedProduct := do
  let env := prepared.finalState.commandState.env
  if env.header.isModule then
    throw <| IO.userError "provisional cached staging only supports non-module source"
  let inventory ← inventoryLocals env request.expectedNames
  assertOptions prepared.finalOpts
  let some provisionalName := request.provisionalOlean
    | throw <| IO.userError "cached audit requires an explicit provisional olean path"
  let provisional : System.FilePath := ⟨provisionalName⟩
  checkProvisionalPath request provisional
  bindInputs request prepared.sourceBytes prepared.setupBytes
  let provisionalC ← if request.cFile.isSome then do
      let path := provisional.addExtension "c"
      if ← path.pathExists then
        throw <| IO.userError "refusing existing provisional C output"
      emitSourceC request env prepared.setup.name path
      pure (some path)
    else pure none
  let provisionalIlean ← if request.ilean.isSome then do
      let path := provisional.addExtension "ilean"
      if ← path.pathExists then
        throw <| IO.userError "refusing existing provisional ilean output"
      writeIlean request prepared path
      pure (some path)
    else pure none
  -- Reset and populate the real stock final-module frequency cache after all EOF
  -- and local declaration guards. The higher budget only governs metadata MetaM.
  warmSymbolFrequency env prepared.finalOpts request.metadataMaxHeartbeats
  prototypeEvent "provisional_export_begin" [("constant_count", toJson inventory.names.size)]
  exportWithMetadataBaseline env provisional true true
  prototypeEvent "provisional_export_complete" [("path", toJson provisional.toString)]
  bindInputs request prepared.sourceBytes prepared.setupBytes
  assertState prepared.finalState.commandState prepared.setup.name request.infoEnabled
  return { moduleName := prepared.setup.name, setup := prepared.setup, opts := prepared.finalOpts
           inventory, sourceBytes := prepared.sourceBytes, setupBytes := prepared.setupBytes
           counts := prepared.result.counts, eofByte := prepared.result.eofByte
           provisional, provisionalC, provisionalIlean }

-- Production entry keeps the fixed heavy-module/request-path gate. The shared
-- staging helper can be tested using import all on owned non-module fixtures.
def stageCachedSource (request : Request) : IO StagedCachedProduct := do
  let prepared ← prepareSource request
  assertCachedHeavyTarget request prepared.finalState.commandState.env
  stagePreparedNonmodule request prepared

-- Public helper enables later owned toy validation without weakening the actual
-- request entry's exact-heavy gate. No private collector is copied or accessed.
unsafe def auditCachedProduct (product : StagedCachedProduct) : IO Json := do
  assertOptions product.opts
  prototypeEvent "cached_import_begin"
    [("constant_count", toJson product.inventory.names.size)]
  let arts := product.setup.importArts.insert product.moduleName
    (ImportArtifacts.ofArray #[product.provisional])
  -- The first header import consumes the stock initializer permission in
  -- withImporting.finally; each later loadExts import must enable it anew.
  enableInitializersExecution
  let cached ← importModules #[{ module := product.moduleName : Import }] product.opts
    (trustLevel := 0) (loadExts := true) (level := .private) (arts := arts)
  if cached.header.trustLevel != 0 || cached.header.isModule then
    throw <| IO.userError "cached import changed trust or non-module import level"
  let some moduleIdx := cached.getModuleIdx? product.moduleName
    | throw <| IO.userError "provisional module absent after exact-artifact import"
  let some moduleData := cached.header.moduleData[moduleIdx.toNat]?
    | throw <| IO.userError "provisional module data absent at imported index"
  unless cached.allImportedModuleNames[moduleIdx.toNat]? == some product.moduleName do
    throw <| IO.userError "provisional module index has a different module name"
  if moduleData.isModule then
    throw <| IO.userError "cached audit only supports non-module source artifacts"
  unless moduleData.constNames.qsort Name.lt == product.inventory.names do
    throw <| IO.userError "provisional module constant-name set differs from original Stage2"
  unless moduleData.constants.size == product.inventory.signatures.size do
    throw <| IO.userError "provisional constant payload count differs from original Stage2"
  for original in product.inventory.signatures do
    unless cached.getModuleIdxFor? original.name == some moduleIdx do
      throw <| IO.userError s!"provisional constant belongs to another imported module: {original.name}"
    let some imported := cached.checked.get.find? original.name
      | throw <| IO.userError s!"original constant absent after provisional import: {original.name}"
    unless sameSignature original (signatureOf imported) do
      throw <| IO.userError s!"provisional signature/kind/flags differ from original: {original.name}"
    if imported.isUnsafe || imported.isAxiom then
      throw <| IO.userError s!"provisional import introduced unsafe or axiom: {original.name}"
  prototypeEvent "cached_inventory_signature_equivalent"
    [("module_index", toJson moduleIdx.toNat), ("constant_count", toJson product.inventory.names.size)]
  let mut entries : Array Json := #[]
  for name in product.inventory.names do
    -- All imported constants reside in Stage1: saved original Stage2 names define
    -- coverage. Public collectAxioms uses stock imported cache wherever present.
    let (axes, auditState) ← (collectAxioms name : CoreM (Array Name)).toIO
      { fileName := "<prototype-cached-axiom-audit>", fileMap := default,
        options := product.opts } { env := cached }
    let auditCounts ← reportLog auditState.messages
    if auditCounts.errors != 0 || auditCounts.warnings != 0 then
      throw <| IO.userError s!"cached axiom query emitted error/warning for {name}"
    for ax in axes do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throw <| IO.userError s!"unsupported axiom dependency of {name}: {ax}"
    entries := entries.push <| Json.mkObj [("name", toJson name), ("axioms", toJson axes)]
    prototypeEvent "cached_axiom_checked"
      [("index", toJson entries.size), ("name", toJson name), ("axioms", toJson axes)]
  return Json.mkObj [("count", toJson product.inventory.names.size), ("entries", toJson entries)
    , ("audit_method", toJson "stock_exported_axioms_reimport_all_original_constants")
    , ("inventory_signature_equivalent", toJson true)
    , ("proof_body_equality_checked", toJson false), ("module_index", toJson moduleIdx.toNat)]

unsafe def compileCachedRequest (request : Request) : IO Unit := do
  let product ← stageCachedSource request
  -- This boundary occurs after stage1 has returned; no original proof env is in
  -- product, and stage2 never receives the old Frontend.State.
  prototypeEvent "stage1_returned_before_cached_import"
    [("constant_count", toJson product.inventory.names.size)]
  let declarationAudit ← auditCachedProduct product
  bindInputs request product.sourceBytes product.setupBytes
  assertOptions product.opts
  -- All genuine provisional outputs are published only after every closure passes.
  -- Partial publication failures still return nonzero and never write a success report.
  publishProvisional product.provisional ⟨request.olean⟩
  match product.provisionalC, request.cFile with
  | some provisional, some target => publishProvisional provisional ⟨target⟩
  | none, none => pure ()
  | _, _ => throw <| IO.userError "provisional/final C request mismatch"
  match product.provisionalIlean, request.ilean with
  | some provisional, some target => publishProvisional provisional ⟨target⟩
  | none, none => pure ()
  | _, _ => throw <| IO.userError "provisional/final ilean request mismatch"
  writeReport request <| finalReport request product.moduleName product.counts
    product.sourceBytes.size product.eofByte false true declarationAudit

unsafe def compileRequest (request : Request) : IO Unit := do
  if request.postExportCachedAxioms then
    compileCachedRequest request
  else
    let prepared ← prepareSource request
    let env := prepared.finalState.commandState.env
    discard <| inventoryLocals env request.expectedNames
    bindInputs request prepared.sourceBytes prepared.setupBytes
    assertOptions prepared.finalOpts
    if request.prewarmSymbolFrequency then
      warmSymbolFrequency env prepared.finalOpts request.metadataMaxHeartbeats
    let declarationAudit ← auditLocals env request.expectedNames
    bindInputs request prepared.sourceBytes prepared.setupBytes
    exportWithMetadataBaseline env ⟨request.olean⟩
      (!Compiler.compiler.postponeCompile.get prepared.finalOpts) request.prewarmSymbolFrequency
    if let some cFile := request.cFile then
      emitSourceC request env prepared.setup.name ⟨cFile⟩
    if let some ilean := request.ilean then
      writeIlean request prepared ⟨ilean⟩
    writeReport request <| finalReport request prepared.setup.name prepared.result.counts
      prepared.sourceBytes.size prepared.result.eofByte env.header.isModule
      request.prewarmSymbolFrequency declarationAudit

end LowInfo309

-- Unsafe IO is confined to the stock initializer switch required by importModules/loadExts.
-- This neither inserts mathematical constants nor changes kernel checking/trust.
public unsafe def main (args : List String) : IO UInt32 := do
  try
    let [requestPath] := args
      | throw <| IO.userError "usage: lean --run SequentialDriver.lean REQUEST.json"
    enableInitializersExecution
    let raw ← IO.FS.readFile ⟨requestPath⟩
    let request : LowInfo309.Request ←
      match Json.parse raw >>= LowInfo309.requestFromJson with
      | .ok value => pure value
      | .error error => throw <| IO.userError s!"invalid request JSON: {error}"
    LowInfo309.compileRequest request
    return (0 : UInt32)
  catch error =>
    IO.eprintln s!"prototype failed: {error}"
    return (1 : UInt32)
