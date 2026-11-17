module

@[expose] public section
namespace Airbender.Trust

/-! The trusted base is the Lean kernel, its standard axioms, the official Sail model,
    and the definitions and claims in human/. Lake pins the external libraries.
    Clean is imported only by the equivalence leaf. Import and source checks read
    the lists below. The setup JSON reader (`parseSetup`), the grid comparison of the `with grids` setup import and
    the compiled subword and unified fixed-row comparisons in NativeGrid are trusted operations. -/

/-- External module roots from Lean, Mathlib and their dependencies, and the Sail model. -/
def trustedModuleRoots : List String := [
  "Init", "Lean", "Std", "Lake", "Mathlib", "Aesop", "Batteries", "ImportGraph",
  "LeanSearchClient", "Plausible", "ProofWidgets", "Qq", "Sail", "SailRV32"]

/-- Modules allowed to use unsafe evaluation, partial procedures or implementation attributes. -/
def trustedTacticModules : List String := [
  "Human.Import.Exec.Emit",
  "Human.Import.NativeGrid",
  "Human.Import.SetupEmit",
  "Proven.InitsTeardowns.Native.Emit",
  "Proven.OpIndex",
  "Proven.ISA.Equiv.Walk",
  "Proven.ISA.Equiv.Run",
  "Proven.ISA.Equiv.MemLemmas",
  "Proven.Import.GKRCompiler.Import",
  "Proven.Import.GKRCompiler.WiringImport",
  "Proven.Import.GKRProtocol.CleanGenericArgumentsImport",
  "Proven.Import.GKRProtocol.FullArithmeticImport",
  "Proven.Import.GKRProtocol.CleanArithmeticImport",
  "Proven.Import.GKRProtocol.CleanHelperArgumentsImport",
  "Proven.Import.GKRProtocol.CleanLookupArgumentsImport",
  "Proven.Import.GKRProtocol.NumericExpressionDataImport"]

/-- Spec modules that define commands or elaborators that add declarations. Review their code as
    specification: the declarations they add do not appear as source text. -/
def declarationCommandModules : List String := [
  "Human.Import.Exec.Emit",
  "Human.Import.Exec.FastColumns",
  "Human.Import.Exec.InitsTeardowns",
  "Human.Import.NativeGrid",
  "Human.Import.NativeRamProducts",
  "Human.Import.SetupEmit",
  "Human.Import.TranscribeCommand"]

/-- The only spec modules whose import closure contains the Sail model roots `Sail` and `SailRV32`.
    `Human` is the library root, which imports every spec module. -/
def sailModules : List String := [
  "Human",
  "Human.Helpers.Core.Configuration",
  "Human.ISA.Sail.Airbender",
  "Human.ISA.Sail.Checks",
  "Human.ISA.Sail.Interpreter",
  "Human.ISA.Sail.Machine",
  "Human.ISA.Sail.MachineTargets",
  "Human.ISA.Sail.NativeTargets",
  "Human.ISA.Sail.Theorems",
  "Human.ISA.Sail.WholeRun"]

end Airbender.Trust
