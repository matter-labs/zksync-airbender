module

@[expose] public section
namespace Airbender.Trust

/-! The trusted base is the Lean kernel, its standard axioms, the official Sail model,
    and the definitions and claims in human/. Lake pins the external libraries.
    Clean is imported only by the equivalence leaf. Import and source checks read
    the lists below. Compiled setup comparisons in NativeGrid are trusted operations. -/

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

end Airbender.Trust
