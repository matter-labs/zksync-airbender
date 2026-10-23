/-
Exact-module adapter for Lean.Environment.replay. Loading/replay follows the
pinned LeanChecker implementation (MIT; Kim Morrison and Sebastian Ullrich).
Imports are only a starting environment: the Python driver requires separate
successful records for their complete compiled DAG before invoking replay.
-/
import Lean.Replay
import Lean.Util.Path

open Lean

private def writeJson (path : System.FilePath) (value : Json) : IO Unit :=
  IO.FS.writeFile path (value.compress ++ "\n")

private def ownData (module : Name) : IO (Array System.FilePath × Array (ModuleData × CompactedRegion)) := do
  let file ← findOLean module
  unless ← file.pathExists do throw (IO.userError s!"missing exact module: {module}")
  let mut files := #[file]
  let server := OLeanLevel.server.adjustFileName file
  let priv := OLeanLevel.private.adjustFileName file
  if ← server.pathExists then
    files := files.push server
    if ← priv.pathExists then files := files.push priv
  else if ← priv.pathExists then
    throw (IO.userError s!"private module part without server part: {module}")
  let parts ← readModuleDataParts files
  if parts.isEmpty then throw (IO.userError "empty compiled module data")
  pure (files, parts)

private def constantMap (data : ModuleData) : IO (Std.HashMap Name ConstantInfo) := do
  unless data.constNames.size == data.constants.size do
    throw (IO.userError "constant-name/data length mismatch")
  let mut constants := {}
  for name in data.constNames, info in data.constants do
    unless name == info.name do throw (IO.userError "constant-name/data mismatch")
    if constants.contains name then throw (IO.userError s!"duplicate local constant: {name}")
    constants := constants.insert name info
  pure constants

private def importJson (imp : Import) : Json := Json.mkObj [
  ("module", toJson imp.module.toString), ("importAll", toJson imp.importAll),
  ("isExported", toJson imp.isExported), ("isMeta", toJson imp.isMeta)]

private def summary (module : Name) (files : Array System.FilePath)
    (data : ModuleData) (constants : Std.HashMap Name ConstantInfo) : Json := Id.run do
  let mut safe : Array String := #[]
  let mut skipped : Array Json := #[]
  let mut skippedUses : Array Json := #[]
  let mut uses : Array Json := #[]
  let mut axioms : Array String := #[]
  for (name, info) in constants.toList do
    if info.isUnsafe || info.isPartial then
      skipped := skipped.push <| Json.mkObj [("name", toJson name.toString),
        ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial)]
    else
      safe := safe.push name.toString
      let dependencies := info.getUsedConstantsAsSet.toArray.qsort Name.lt
      uses := uses.push <| Json.mkObj [("user", toJson name.toString),
        ("uses", toJson (dependencies.map Name.toString))]
      for dependency in dependencies do
        if let some target := constants[dependency]? then
          if target.isUnsafe || target.isPartial then
            skippedUses := skippedUses.push <| Json.mkObj [("user", toJson name.toString),
              ("dependency", toJson dependency.toString)]
    if info matches .axiomInfo _ then axioms := axioms.push name.toString
  return Json.mkObj [("schema", toJson "airbender-kernel-replay-v1"),
    ("module", toJson module.toString), ("files", toJson (files.map System.FilePath.toString)),
    ("imports", .arr (data.imports.map importJson)), ("isModule", toJson data.isModule),
    ("codegenOnly", toJson (data.extraConstNames.map Name.toString)),
    ("safe", toJson (safe.qsort (· < ·))),
    ("skipped", .arr skipped), ("dependencies", .arr uses),
    ("skippedDependencyUses", .arr skippedUses), ("axioms", toJson axioms)]

private def inspect (module : Name) (output : System.FilePath) : IO Unit := do
  let (files, parts) ← ownData module
  let some (first, _) := parts[0]? | throw (IO.userError "missing exported module data")
  let some (last, _) := parts[parts.size - 1]? | throw (IO.userError "missing most-private module data")
  let constants ← constantMap last
  unless first.imports == last.imports do throw (IO.userError "compiled-part import headers differ")
  writeJson output (summary module files last constants)

private unsafe def replay (module : Name) (output : System.FilePath) : IO UInt32 := do
  let (files, parts) ← ownData module
  let some (data, _) := parts[0]? | throw (IO.userError "missing exported module data")
  let some (last, _) := parts[parts.size - 1]? | throw (IO.userError "missing most-private module data")
  let constants ← constantMap last
  unless data.imports == last.imports do throw (IO.userError "compiled-part import headers differ")
  let (_, state) ← importModulesCore data.imports |>.run
  let env ← finalizeImport state data.imports {} 0 false false (isModule := true)
  -- Missing dependencies are API/coverage failures, never successful negative controls.
  for (_, info) in constants.toList do
    unless info.isUnsafe || info.isPartial do
      for dependency in info.getUsedConstantsAsSet do
        unless constants.contains dependency || (env.find? dependency).isSome do
          throw (IO.userError s!"missing replay dependency: {dependency}")
  try
    let checked ← env.replay constants
    let report := summary module files last constants
    let fields ← match report.getObj? with
      | .ok fields => pure fields.toList
      | .error error => throw (IO.userError error)
    writeJson output (Json.mkObj (("status", toJson "pass") :: fields))
    checked.freeRegions
    pure 0
  catch error =>
    IO.eprintln s!"KERNEL_REPLAY_REJECTED {module}: {error}"
    pure 1

unsafe def main (args : List String) : IO UInt32 := do
  try
    let some sysroot ← IO.getEnv "LEAN_SYSROOT" |
      throw (IO.userError "set LEAN_SYSROOT explicitly")
    Lean.initSearchPath sysroot
    if let some extra ← IO.getEnv "AIRBENDER_ASSURANCE_PATH" then
      Lean.searchPathRef.modify fun paths => System.SearchPath.parse extra ++ paths
    match args with
    | ["paths", output] =>
      writeJson output (toJson ((← searchPathRef.get).map System.FilePath.toString)); pure 0
    | ["inspect", module, output] => inspect module.toName output; pure 0
    | ["replay", module, output] => replay module.toName output
    | _ => throw (IO.userError "usage: KernelReplay.lean paths OUT | inspect MODULE OUT | replay MODULE OUT")
  catch error =>
    IO.eprintln s!"KERNEL_REPLAY_API_ERROR {error}"
    pure 2
