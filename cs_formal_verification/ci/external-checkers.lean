module
import all Lake.CLI.Check

set_option warningAsError true

/-- Use Lake's sandbox, export format and checker settings for an advisory replay. -/
private def checkerContext (toolchain sandbox project : System.FilePath) : Lake.Check.Context := {
  projectDir := project
  challengeModule := .anonymous
  solutionModule := .anonymous
  theoremNames := #[]
  definitionNames := #[]
  legalAxioms := #[`propext, `Quot.sound, `Classical.choice]
  leanPrefix := toolchain
  leanPath := ""
  binPath := ""
  whichSandbox := .path sandbox.toString
  whichLake := toolchain / "bin" / "lake"
  lakeHome := toolchain
  whichLean4Export := toolchain / "bin" / "lean4export"
  whichLeanChecker := toolchain / "bin" / "leanchecker"
  whichEnvBin := "/usr/bin/env"
  externalKernels := {}
  bundledKernels := #[]
  moduleStore := {}
}

/-- Run all four external checkers on the same complete export. -/
public def main (args : List String) : IO UInt32 := do
  let [exportName, sandboxName, prefixName] := args
    | throw (IO.userError "usage: external-checkers.lean EXPORT SANDBOX TOOLCHAIN")
  let exportPath : System.FilePath := exportName
  unless ← exportPath.pathExists do
    IO.eprintln "The retained kernel export is missing."
    return 2
  let empty ← IO.FS.withFile exportPath .read fun handle => do
    return (← handle.read 1).isEmpty
  if empty then
    IO.eprintln "The retained kernel export is empty."
    return 2
  let toolchain : System.FilePath := prefixName
  let context := checkerContext toolchain sandboxName (← IO.currentDir)
  let checkers := #[
    ("lean4lean", #[ (toolchain / "bin" / "lean4lean").toString, "--import"]),
    ("nanoda", #[ (toolchain / "bin" / "nanoda_bin").toString]),
    ("con-leche", #[ (toolchain / "bin" / "con-leche").toString]),
    ("con-ron", #[ (toolchain / "bin" / "con-ron").toString])]
  let mut failures : Array String := #[]
  for (name, command) in checkers do
    if let some reason ← (Lake.Check.runExternalKernel name command exportPath).run context then
      failures := failures.push reason
  for reason in failures do
    IO.eprintln reason
  return if failures.isEmpty then 0 else 1
