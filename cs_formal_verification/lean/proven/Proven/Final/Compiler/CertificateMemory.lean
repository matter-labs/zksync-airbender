module
public import Human.Compiler.CertificateMemory
public import Proven.Final.Compiler.MemoryPorts
public import Proven.Final.Compiler.WorkerMemoryPorts
public import Proven.GKRProtocol.MemoryPortsNative.AddSubCached
public import Proven.GKRProtocol.MemoryPortsNative.JumpBranchCached
public import Proven.GKRProtocol.MemoryPortsNative.MulDivCached
public import Proven.GKRProtocol.MemoryPortsNative.ShiftBinopCached
public import Proven.GKRProtocol.MemoryPortsNative.SubwordMemoryCached
public import Proven.GKRProtocol.MemoryPortsNative.WordMemoryCached
public import Proven.GKRProtocol.MemoryPortsNative.UnifiedCached
public import Proven.Compiler.WorkerWitnesses.Standard
public import Proven.NonVacuous.UnrolledNative.Certificates
public import Proven.NonVacuous.PaddedNative.Unified

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.MemoryPortsNative.AddSubCached
open Airbender Airbender.Compiler NativeMemoryBridge
set_option maxRecDepth 32768

/-- The canonical extension values of native base values meet the extension semantics of the capture. -/
theorem canonical_holds {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Captures.AddSub.imported.circuit physical) :
    NativeMemory.Holds Captures.AddSub.imported.circuit challenges physical
      (FunctionalNative.AddSubCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 physical) := by
  let values := FunctionalNative.AddSubCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 physical
  have same : wires challenges (baseRoles ConsumerNative.AddSubCached.native.typing) physical values = values :=
    (wires_typed _ _ _ _).trans
      (FunctionalLinksNative.AddSubCached.native.assignment_value challenges.memory.embed (cacheChallenges challenges) 0 physical)
  show NativeMemory.Holds _ challenges physical values
  rw [← same]
  apply holds_of_programs challenges _ physical values typed
  · rw [same, ← definitions_binding, ← FunctionalLinksNative.AddSubCached.native.memoryDefinitionsAgree]
    exact FunctionalNative.AddSubCached.native.canonical_affines _ _ 0 physical
      (NativeBindings.AddSub.scalar_gates physical accepted)
  · rw [same, ← gates_binding]
    exact FunctionalNative.AddSubCached.native.canonical_products _ _ 0 physical

end Airbender.Compiler.MemoryPortsNative.AddSubCached

namespace Airbender.Compiler.MemoryPortsNative.JumpBranchCached
open Airbender Airbender.Compiler NativeMemoryBridge
set_option maxRecDepth 32768

/-- The canonical extension values of native base values meet the extension semantics of the capture. -/
theorem canonical_holds {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Captures.JumpBranch.imported.circuit physical) :
    NativeMemory.Holds Captures.JumpBranch.imported.circuit challenges physical
      (FunctionalNative.JumpBranchCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 physical) := by
  let values := FunctionalNative.JumpBranchCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 physical
  have same : wires challenges (baseRoles ConsumerNative.JumpBranchCached.native.typing) physical values = values :=
    (wires_typed _ _ _ _).trans
      (FunctionalLinksNative.JumpBranchCached.native.assignment_value challenges.memory.embed (cacheChallenges challenges) 0 physical)
  show NativeMemory.Holds _ challenges physical values
  rw [← same]
  apply holds_of_programs challenges _ physical values typed
  · rw [same, ← definitions_binding, ← FunctionalLinksNative.JumpBranchCached.native.memoryDefinitionsAgree]
    exact FunctionalNative.JumpBranchCached.native.canonical_affines _ _ 0 physical
      (NativeBindings.JumpBranch.scalar_gates physical accepted)
  · rw [same, ← gates_binding]
    exact FunctionalNative.JumpBranchCached.native.canonical_products _ _ 0 physical

end Airbender.Compiler.MemoryPortsNative.JumpBranchCached

namespace Airbender.Compiler.MemoryPortsNative.MulDivCached
open Airbender Airbender.Compiler NativeMemoryBridge
set_option maxRecDepth 32768

/-- The canonical extension values of native base values meet the extension semantics of the capture. -/
theorem canonical_holds {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Captures.MulDiv.imported.circuit physical) :
    NativeMemory.Holds Captures.MulDiv.imported.circuit challenges physical
      (FunctionalNative.MulDivCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 physical) := by
  let values := FunctionalNative.MulDivCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 physical
  have same : wires challenges (baseRoles ConsumerNative.MulDivCached.native.typing) physical values = values :=
    (wires_typed _ _ _ _).trans
      (FunctionalLinksNative.MulDivCached.native.assignment_value challenges.memory.embed (cacheChallenges challenges) 0 physical)
  show NativeMemory.Holds _ challenges physical values
  rw [← same]
  apply holds_of_programs challenges _ physical values typed
  · rw [same, ← definitions_binding, ← FunctionalLinksNative.MulDivCached.native.memoryDefinitionsAgree]
    exact FunctionalNative.MulDivCached.native.canonical_affines _ _ 0 physical
      (NativeBindings.MulDiv.scalar_gates physical accepted)
  · rw [same, ← gates_binding]
    exact FunctionalNative.MulDivCached.native.canonical_products _ _ 0 physical

end Airbender.Compiler.MemoryPortsNative.MulDivCached

namespace Airbender.Compiler.MemoryPortsNative.ShiftBinopCached
open Airbender Airbender.Compiler NativeMemoryBridge
set_option maxRecDepth 32768

/-- The canonical extension values of native base values meet the extension semantics of the capture. -/
theorem canonical_holds {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Captures.ShiftBinop.imported.circuit physical) :
    NativeMemory.Holds Captures.ShiftBinop.imported.circuit challenges physical
      (FunctionalNative.ShiftBinopCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 physical) := by
  let values := FunctionalNative.ShiftBinopCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 physical
  have same : wires challenges (baseRoles ConsumerNative.ShiftBinopCached.native.typing) physical values = values :=
    (wires_typed _ _ _ _).trans
      (FunctionalLinksNative.ShiftBinopCached.native.assignment_value challenges.memory.embed (cacheChallenges challenges) 0 physical)
  show NativeMemory.Holds _ challenges physical values
  rw [← same]
  apply holds_of_programs challenges _ physical values typed
  · rw [same, ← definitions_binding, ← FunctionalLinksNative.ShiftBinopCached.native.memoryDefinitionsAgree]
    exact FunctionalNative.ShiftBinopCached.native.canonical_affines _ _ 0 physical
      (NativeBindings.ShiftBinop.scalar_gates physical accepted)
  · rw [same, ← gates_binding]
    exact FunctionalNative.ShiftBinopCached.native.canonical_products _ _ 0 physical

end Airbender.Compiler.MemoryPortsNative.ShiftBinopCached

namespace Airbender.Compiler.MemoryPortsNative.SubwordMemoryCached
open Airbender Airbender.Compiler NativeMemoryBridge
set_option maxRecDepth 32768

/-- The canonical extension values of native base values meet the extension semantics of the capture. -/
theorem canonical_holds {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Captures.SubwordMemory.imported.circuit physical) :
    NativeMemory.Holds Captures.SubwordMemory.imported.circuit challenges physical
      (FunctionalNative.SubwordMemoryCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 physical) := by
  let values := FunctionalNative.SubwordMemoryCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 physical
  have same : wires challenges (baseRoles ConsumerNative.SubwordMemoryCached.native.typing) physical values = values :=
    (wires_typed _ _ _ _).trans
      (FunctionalLinksNative.SubwordMemoryCached.native.assignment_value challenges.memory.embed (cacheChallenges challenges) 0 physical)
  show NativeMemory.Holds _ challenges physical values
  rw [← same]
  apply holds_of_programs challenges _ physical values typed
  · rw [same, ← definitions_binding, ← FunctionalLinksNative.SubwordMemoryCached.native.memoryDefinitionsAgree]
    exact FunctionalNative.SubwordMemoryCached.native.canonical_affines _ _ 0 physical
      (NativeBindings.SubwordMemory.scalar_gates physical accepted)
  · rw [same, ← gates_binding]
    exact FunctionalNative.SubwordMemoryCached.native.canonical_products _ _ 0 physical

end Airbender.Compiler.MemoryPortsNative.SubwordMemoryCached

namespace Airbender.Compiler.MemoryPortsNative.WordMemoryCached
open Airbender Airbender.Compiler NativeMemoryBridge
set_option maxRecDepth 32768

/-- The canonical extension values of native base values meet the extension semantics of the capture. -/
theorem canonical_holds {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Captures.WordMemory.imported.circuit physical) :
    NativeMemory.Holds Captures.WordMemory.imported.circuit challenges physical
      (FunctionalNative.WordMemoryCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 physical) := by
  let values := FunctionalNative.WordMemoryCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 physical
  have same : wires challenges (baseRoles ConsumerNative.WordMemoryCached.native.typing) physical values = values :=
    (wires_typed _ _ _ _).trans
      (FunctionalLinksNative.WordMemoryCached.native.assignment_value challenges.memory.embed (cacheChallenges challenges) 0 physical)
  show NativeMemory.Holds _ challenges physical values
  rw [← same]
  apply holds_of_programs challenges _ physical values typed
  · rw [same, ← definitions_binding, ← FunctionalLinksNative.WordMemoryCached.native.memoryDefinitionsAgree]
    exact FunctionalNative.WordMemoryCached.native.canonical_affines _ _ 0 physical
      (NativeBindings.WordMemory.scalar_gates physical accepted)
  · rw [same, ← gates_binding]
    exact FunctionalNative.WordMemoryCached.native.canonical_products _ _ 0 physical

end Airbender.Compiler.MemoryPortsNative.WordMemoryCached

namespace Airbender.Compiler.MemoryPortsNative.UnifiedCached
open Airbender Airbender.Compiler NativeMemoryBridge
set_option maxRecDepth 32768

/-- The canonical extension values of native base values meet the extension semantics of the capture. -/
theorem canonical_holds {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Captures.Unified.imported.circuit physical) :
    NativeMemory.Holds Captures.Unified.imported.circuit challenges physical
      (FunctionalNative.UnifiedCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 physical) := by
  let values := FunctionalNative.UnifiedCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 physical
  have same : wires challenges (baseRoles ConsumerNative.UnifiedCached.native.typing) physical values = values :=
    (wires_typed _ _ _ _).trans
      (FunctionalLinksNative.UnifiedCached.native.assignment_value challenges.memory.embed (cacheChallenges challenges) 0 physical)
  show NativeMemory.Holds _ challenges physical values
  rw [← same]
  apply holds_of_programs challenges _ physical values typed
  · rw [same, ← definitions_binding, ← FunctionalLinksNative.UnifiedCached.native.memoryDefinitionsAgree]
    exact FunctionalNative.UnifiedCached.native.canonical_affines _ _ 0 physical
      (NativeBindings.Unified.scalar_gates physical accepted)
  · rw [same, ← gates_binding]
    exact FunctionalNative.UnifiedCached.native.canonical_products _ _ 0 physical

end Airbender.Compiler.MemoryPortsNative.UnifiedCached

namespace Airbender.Compiler
open Trace NativeMemoryBridge

/-- A fixed challenge set over the base field for the witnesses. -/
def sampleChallenges : NativeMemory.Challenges NativeArithmetic.F := ⟨⟨RingHom.id _, 0, fun _ => 0, fun _ => 0⟩, 0⟩

/-- The canonical extension values of a cached CPU certificate. -/
noncomputable def programCanonical {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    {tables : ProgramLookupRows} (cert : ProgramRowCertificate tables) : GKRAddress → E :=
  match cert.row.family with
  | .addSub =>
    FunctionalNative.AddSubCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 cert.physical
  | .jumpBranchSlt =>
    FunctionalNative.JumpBranchCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 cert.physical
  | .mulDiv =>
    FunctionalNative.MulDivCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 cert.physical
  | .shiftBinop =>
    FunctionalNative.ShiftBinopCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 cert.physical
  | .subwordMemory =>
    FunctionalNative.SubwordMemoryCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 cert.physical
  | .wordMemory =>
    FunctionalNative.WordMemoryCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 cert.physical

/-- The canonical extension values of a cached CPU certificate meet the extension semantics. -/
theorem programCanonical_holds {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    {tables : ProgramLookupRows} (cert : ProgramRowCertificate tables) :
    NativeMemory.Holds (NativeLookups.circuitFor (.pooled cert.row.family)) challenges cert.physical
      (programCanonical challenges cert) := by
  obtain ⟨⟨family, assignment⟩, physical, arithmetic, _, _⟩ := cert
  cases family
  case addSub => exact MemoryPortsNative.AddSubCached.canonical_holds challenges physical arithmetic
  case jumpBranchSlt => exact MemoryPortsNative.JumpBranchCached.canonical_holds challenges physical arithmetic
  case mulDiv => exact MemoryPortsNative.MulDivCached.canonical_holds challenges physical arithmetic
  case shiftBinop => exact MemoryPortsNative.ShiftBinopCached.canonical_holds challenges physical arithmetic
  case subwordMemory => exact MemoryPortsNative.SubwordMemoryCached.canonical_holds challenges physical arithmetic
  case wordMemory => exact MemoryPortsNative.WordMemoryCached.canonical_holds challenges physical arithmetic

/-- The canonical extension values of a cached unified certificate. -/
noncomputable def unifiedCanonical {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    {tables : ProgramLookupRows} (cert : UnifiedRowCertificate tables) : GKRAddress → E :=
  FunctionalNative.UnifiedCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0
    cert.physical

/-- The canonical extension values of a cached unified certificate meet the extension semantics. -/
theorem unifiedCanonical_holds {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    {tables : ProgramLookupRows} (cert : UnifiedRowCertificate tables) :
    NativeMemory.Holds (NativeLookups.circuitFor .unified) challenges cert.physical
      (unifiedCanonical challenges cert) :=
  MemoryPortsNative.UnifiedCached.canonical_holds challenges cert.physical cert.arithmetic

/-- The program values of a cached worker certificate. -/
noncomputable def workerProgramValues {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    (cert : WorkerRowCertificate) : GKRAddress → E :=
  match cert.family with
  | .bigint => programValues WorkerPortsNative.BigintCached.roles WorkerPortsNative.BigintCached.circuit challenges
    cert.physical
  | .blakeG => programValues WorkerPortsNative.BlakeGCached.roles WorkerPortsNative.BlakeGCached.circuit challenges
    cert.physical
  | .blakeRound => programValues WorkerPortsNative.BlakeRoundCached.roles WorkerPortsNative.BlakeRoundCached.circuit challenges
    cert.physical
  | .columnParity => programValues WorkerPortsNative.KeccakColumnParityCached.roles WorkerPortsNative.KeccakColumnParityCached.circuit challenges
    cert.physical
  | .thetaRho => programValues WorkerPortsNative.KeccakThetaRhoCached.roles WorkerPortsNative.KeccakThetaRhoCached.circuit challenges
    cert.physical
  | .chi5 => programValues WorkerPortsNative.KeccakChi5Cached.roles WorkerPortsNative.KeccakChi5Cached.circuit challenges
    cert.physical

/-- The program values of a cached worker certificate meet the extension semantics. -/
theorem workerProgramValues_holds {E : Type} [CommRing E] (challenges : NativeMemory.Challenges E)
    (cert : WorkerRowCertificate) :
    NativeMemory.Holds (NativeWorkerLookups.circuitFor cert.family) challenges cert.physical
      (workerProgramValues challenges cert) := by
  obtain ⟨family, assignment, physical, _, _, _⟩ := cert
  cases family
  · exact program_holds challenges _ physical WorkerPortsNative.BigintCached.program_valid
      WorkerPortsNative.BigintCached.program_covered WorkerPortsNative.BigintCached.typed
  · exact program_holds challenges _ physical WorkerPortsNative.BlakeGCached.program_valid
      WorkerPortsNative.BlakeGCached.program_covered WorkerPortsNative.BlakeGCached.typed
  · exact program_holds challenges _ physical WorkerPortsNative.BlakeRoundCached.program_valid
      WorkerPortsNative.BlakeRoundCached.program_covered WorkerPortsNative.BlakeRoundCached.typed
  · exact program_holds challenges _ physical WorkerPortsNative.KeccakColumnParityCached.program_valid
      WorkerPortsNative.KeccakColumnParityCached.program_covered WorkerPortsNative.KeccakColumnParityCached.typed
  · exact program_holds challenges _ physical WorkerPortsNative.KeccakThetaRhoCached.program_valid
      WorkerPortsNative.KeccakThetaRhoCached.program_covered WorkerPortsNative.KeccakThetaRhoCached.typed
  · exact program_holds challenges _ physical WorkerPortsNative.KeccakChi5Cached.program_valid
      WorkerPortsNative.KeccakChi5Cached.program_covered WorkerPortsNative.KeccakChi5Cached.typed

/-- Native gates, placement and extension values of a cached CPU certificate give the RAM outputs of its row. -/
theorem program_certificate_ram_products : ProgramCertificateRamProductsClaim := by
  intro E _ challenges tables cert values holds
  obtain ⟨⟨family, assignment⟩, physical, arithmetic, placement, _⟩ := cert
  cases family
  · exact addSub_cached_memory challenges physical values ⟨.addSub, assignment⟩ rfl arithmetic placement holds
  · exact wordMemory_cached_memory challenges physical values ⟨.wordMemory, assignment⟩ rfl arithmetic placement holds
  · exact jumpBranch_cached_memory challenges physical values ⟨.jumpBranchSlt, assignment⟩ rfl arithmetic placement
      holds
  · exact mulDiv_cached_memory challenges physical values ⟨.mulDiv, assignment⟩ rfl arithmetic placement holds
  · exact shiftBinop_cached_memory challenges physical values ⟨.shiftBinop, assignment⟩ rfl arithmetic placement holds
  · exact subwordMemory_cached_memory challenges physical values ⟨.subwordMemory, assignment⟩ rfl arithmetic placement
      holds

/-- The canonical extension values of the ADD certificate meet the extension semantics. -/
theorem program_certificate_ram_products_satisfiable : ProgramCertificateRamProductsSatisfiableClaim :=
  ⟨sampleChallenges, _, NonVacuous.UnrolledNative.rowCertificate.toProgramRowCertificate, _,
    programCanonical_holds sampleChallenges _⟩

/-- Native gates, placement and extension values of a cached unified certificate give the RAM outputs of its
    row. -/
theorem unified_certificate_ram_products : UnifiedCertificateRamProductsClaim := by
  intro E _ challenges tables cert values holds
  obtain ⟨⟨family, assignment⟩, physical, arithmetic, placement, _⟩ := cert
  cases family
  exact unified_cached_memory challenges physical values ⟨.machine, assignment⟩ arithmetic placement holds

/-- The canonical extension values of the unified ADD certificate meet the extension semantics. -/
theorem unified_certificate_ram_products_satisfiable : UnifiedCertificateRamProductsSatisfiableClaim :=
  ⟨sampleChallenges, _, NonVacuous.PaddedNative.unifiedRowCertificate.toUnifiedRowCertificate, _,
    unifiedCanonical_holds sampleChallenges _⟩

/-- Native gates, placement and extension values of a cached worker certificate give the RAM outputs of its
    row. -/
theorem worker_certificate_ram_products : WorkerCertificateRamProductsClaim := by
  intro E _ challenges cert values holds
  obtain ⟨family, assignment, physical, arithmetic, placement, _⟩ := cert
  cases family
  · refine ⟨fun row found => ?_, fun row found => by simp [WorkerRowCertificate.splitRow] at found⟩
    cases found
    exact bigint_cached_memory challenges physical values ⟨.bigint, assignment⟩ rfl arithmetic placement holds
  · refine ⟨fun row found => ?_, fun row found => by simp [WorkerRowCertificate.splitRow] at found⟩
    cases found
    exact blakeG_cached_memory challenges physical values ⟨.blakeG, assignment⟩ rfl arithmetic placement holds
  · refine ⟨fun row found => ?_, fun row found => by simp [WorkerRowCertificate.splitRow] at found⟩
    cases found
    exact blakeRound_cached_memory challenges physical values ⟨.blakeRound, assignment⟩ rfl arithmetic placement holds
  · refine ⟨fun row found => by simp [WorkerRowCertificate.standardRow] at found, fun row found => ?_⟩
    cases found
    exact keccakColumnParity_cached_memory challenges physical values ⟨.columnParity, assignment⟩ rfl arithmetic
      placement holds
  · refine ⟨fun row found => by simp [WorkerRowCertificate.standardRow] at found, fun row found => ?_⟩
    cases found
    exact keccakThetaRho_cached_memory challenges physical values ⟨.thetaRho, assignment⟩ rfl arithmetic placement
      holds
  · refine ⟨fun row found => by simp [WorkerRowCertificate.standardRow] at found, fun row found => ?_⟩
    cases found
    exact keccakChi5_cached_memory challenges physical values ⟨.chi5, assignment⟩ rfl arithmetic placement holds

/-- The program values of the bigint certificate meet the extension semantics. -/
theorem worker_certificate_ram_products_satisfiable : WorkerCertificateRamProductsSatisfiableClaim :=
  ⟨sampleChallenges, WorkerWitnesses.bigint.toWorkerRowCertificate, _, workerProgramValues_holds sampleChallenges _⟩

end Airbender.Compiler
