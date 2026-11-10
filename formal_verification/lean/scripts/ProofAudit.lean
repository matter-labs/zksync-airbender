import Airbender.Checks.ProofInventory
import Lean.Data.Json

open Lean Airbender.Checks.ProofInventory

private def asIO (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def emit (handle : IO.FS.Handle) (fields : List (String × Json)) : IO Unit :=
  handle.putStrLn (Json.mkObj fields).compress

private def copyText (text : String) : String := String.ofList text.toList

/-- Executable roots come from the frozen Lake configuration. Isolated controls
may supply their own roots. This chooses compatible import contexts only;
proof/root/axiom selection still uses every actual compiled environment. -/
private def entrypoints (request : Json) : IO (Array Name) := do
  if let .ok configured := request.getObjVal? "entrypoints" then
    let names : Array String ← asIO (fromJson? configured)
    return names.map String.toName
  let result ← IO.Process.output {
    cmd := "python3"
    args := #["-c", "import json,tomllib;from pathlib import Path;d=tomllib.loads(Path('lakefile.toml').read_text());print(json.dumps([e.get('root',e['name']) for e in d.get('lean_exe',[])]))"] }
  unless result.exitCode == 0 do
    throw (IO.userError s!"cannot read configured executable roots: {result.stderr}")
  let names : Array String ← asIO (fromJson? (← asIO (Json.parse result.stdout)))
  return names.map String.toName

/-- Inspect every requested module. Independent executables need independent
import contexts because their global main declarations need not agree.
Unexpected conflicts within the remaining context still fail closed in Lean. -/
private def contexts (modules executableRoots : Array Name) : Array (Array Name) := Id.run do
  let common := modules.filter fun moduleName => !executableRoots.contains moduleName
  let executable := modules.filter executableRoots.contains
  if executable.isEmpty then return if common.isEmpty then #[] else #[common]
  let mut result := #[]
  for index in [:executable.size] do
    let group := #[executable[index]!]
    result := result.push (if index + 1 == executable.size then group ++ common else group)
  return result

private def structuralName : Name → Json
  | .anonymous => toJson "anonymous"
  | .str parent text => .arr #[toJson "str", structuralName parent, toJson text]
  | .num parent number => .arr #[toJson "num", structuralName parent, toJson (toString number)]

private structure AuditState where
  identities : Std.HashMap String (String × String) := {}
  records : Std.HashMap String String := {}
  resolved : Std.HashSet String := {}
  covered : Std.HashSet Name := {}
  roots : Nat := 0
  declarations : Nat := 0

/-- Only copied structural names and serialized graph records survive a context.
A repeated printed name must denote the same declaration, not another executable. -/
private def record (handle : IO.FS.Handle) (requested : Std.HashSet String)
    (state : AuditState) (name : Name) (moduleOrigin kind : String)
    (fields : List (String × Json)) : IO AuditState := do
  let printed := copyText name.toString
  let shape := copyText ((structuralName name).compress)
  let moduleOrigin := copyText moduleOrigin
  if let some (previousShape, previousOrigin) := state.identities[printed]? then
    unless previousShape == shape && previousOrigin == moduleOrigin do
      if requested.contains printed then
        throw (IO.userError s!"ambiguous explicit audit root: {printed}")
      throw (IO.userError s!"ambiguous proof/dependency declaration: {printed}")
  let state := { state with identities := state.identities.insert printed (shape, moduleOrigin) }
  let key := kind ++ ":" ++ printed
  let encoded := copyText ((Json.mkObj fields).compress)
  if let some previous := state.records[key]? then
    unless previous == encoded do throw (IO.userError s!"inconsistent audit record: {printed}")
    return state
  handle.putStrLn encoded
  return { state with
    records := state.records.insert key encoded
    roots := state.roots + (if kind == "root" then 1 else 0)
    declarations := state.declarations + (if kind == "declaration" then 1 else 0) }

private def inspectContext (env : Environment) (group : Array Name)
    (requested : Std.HashSet String) (reviewPrefix : String) (handle : IO.FS.Handle)
    (initial : AuditState) : IO AuditState := do
  let mut state := initial
  for moduleName in group do
    unless env.header.moduleNames.contains moduleName do
      throw (IO.userError s!"requested module absent from audit environment: {moduleName}")
    state := { state with covered := state.covered.insert moduleName }
  let mut selected : Std.HashMap Name Bool := {}
  for (name, info) in env.constants.toList do
    if requested.contains name.toString then
      state := { state with resolved := state.resolved.insert (copyText name.toString) }
      selected := selected.insert name true
    if within (origin env name) reviewPrefix then
      if ← isProof env info then
        selected := selected.insert name (selected[name]?.getD false)
      else
        state ← record handle requested state name (origin env name) "review_nonproof"
          [("kind", toJson "review_nonproof"), ("name", toJson name.toString),
           ("origin", toJson (origin env name))]
    if info matches .axiomInfo _ then
      state ← record handle requested state name (origin env name) "present_axiom"
        [("kind", toJson "present_axiom"), ("name", toJson name.toString),
         ("origin", toJson (origin env name))]
  let mut pending : Array Name := #[]
  for (name, explicit) in selected.toList do
    let some info := env.find? name | throw (IO.userError s!"missing selected root: {name}")
    state ← record handle requested state name (origin env name) "root"
      [("kind", toJson "root"), ("name", toJson name.toString),
       ("origin", toJson (origin env name)), ("explicit", toJson explicit),
       ("proofValued", toJson (← isProof env info))]
    pending := pending.push name
  let mut seen : Std.HashSet Name := {}
  let mut position := 0
  while position < pending.size do
    let name := pending[position]!
    position := position + 1
    unless seen.contains name do
      seen := seen.insert name
      let some info := env.find? name | throw (IO.userError s!"missing dependency declaration: {name}")
      let uses := dependencies info
      state ← record handle requested state name (origin env name) "declaration"
        [("kind", toJson "declaration"), ("name", toJson name.toString),
         ("origin", toJson (origin env name)), ("declarationKind", toJson (declarationKind info)),
         ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial),
         ("uses", toJson (uses.map Name.toString))]
      pending := pending ++ uses
  return state

/-- Every requested source is inspected in a real compatible environment. The
merged report remains the same closed, uniquely named dependency graph. -/
private unsafe def audit (request output : System.FilePath) : IO Unit := do
  let request ← asIO (Json.parse (← IO.FS.readFile request))
  let modules : Array String ← asIO (request.getObjValAs? (Array String) "modules")
  let roots : Array String ← asIO (request.getObjValAs? (Array String) "roots")
  let reviewPrefix : String ← asIO (request.getObjValAs? String "reviewPrefix")
  let requested := roots.foldl (fun set name => set.insert name) ({} : Std.HashSet String)
  unless requested.size == roots.size do throw (IO.userError "duplicate explicit audit roots")
  let moduleNames := modules.map String.toName
  let moduleSet := moduleNames.foldl (fun set name => set.insert name) ({} : Std.HashSet Name)
  unless moduleSet.size == moduleNames.size do throw (IO.userError "duplicate requested audit modules")
  let partitions := contexts moduleNames (← entrypoints request)
  IO.FS.withFile output .write fun handle => do
    emit handle [("kind", toJson "header"), ("schema", toJson "airbender-proof-audit-v1"),
      ("explicitRoots", toJson roots.size), ("reviewPrefix", toJson reviewPrefix)]
    let mut state : AuditState := {}
    for group in partitions do
      -- Loaded extensions can retain compacted objects, so this documented
      -- lifetime-scoped API deliberately leaves them unloaded. Meta.isProp
      -- classifies actual stored types using the environment's constants.
      state ← withImportModules (group.map fun moduleName =>
          { module := moduleName, importAll := true }) {} fun env =>
        inspectContext env group requested reviewPrefix handle state
    for root in roots do
      unless state.resolved.contains root do throw (IO.userError s!"missing explicit audit root: {root}")
    unless state.covered.size == moduleNames.size do
      throw (IO.userError "incomplete requested-module audit coverage")
    emit handle [("kind", toJson "footer"), ("roots", toJson state.roots),
      ("declarations", toJson state.declarations), ("modules", toJson state.covered.size),
      ("contexts", toJson partitions.size)]

unsafe def main (args : List String) : IO UInt32 := do
  try
    let some sysroot ← IO.getEnv "LEAN_SYSROOT" |
      throw (IO.userError "set LEAN_SYSROOT explicitly")
    Lean.initSearchPath sysroot
    if let some extra ← IO.getEnv "AIRBENDER_ASSURANCE_PATH" then
      Lean.searchPathRef.modify fun paths => System.SearchPath.parse extra ++ paths
    Lean.enableInitializersExecution
    match args with
    | [request, output] => audit request output; pure 0
    | _ => throw (IO.userError "usage: ProofAudit.lean REQUEST.json OUTPUT.jsonl")
  catch error =>
    IO.eprintln s!"PROOF_AUDIT_ERROR {error}"
    pure 1
