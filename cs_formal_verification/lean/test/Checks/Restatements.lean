module
public import Proven.Final.Circuits.AddSub.RVTheorems
public import Proven.Final.Circuits.JumpBranchSlt.RVTheorems
public import Proven.Final.Circuits.MulDiv.RVTheorems
public import Proven.Final.Circuits.ShiftBinop.RVTheorems
public import Proven.Final.Circuits.SubwordMemory.RVTheorems
public import Proven.Final.Circuits.WordMemory.RVTheorems
public import Proven.Final.Trace.Families.AddSub.RVTheorems
public import Proven.Final.Trace.Families.JumpBranchSlt.RVTheorems
public import Proven.Final.Trace.Families.MulDiv.RVTheorems
public import Proven.Final.Trace.Families.ShiftBinop.RVTheorems
public import Proven.Final.Trace.Families.SubwordMemory.RVTheorems
public import Proven.Final.Circuits.Bigint.RVTheorems
public import Proven.Final.Circuits.Blake2G.Theorems
public import Proven.Final.Circuits.InitsTeardowns.Theorems

@[expose] public section

/-! Equivalence checks for the reviewed claim statements. -/

namespace Checks.Restatements
open Airbender Airbender.Trace

/-- The shape of the per-row RV claims: for every public setup meeting `assumptions`, every row the model relates
    satisfies `conclusion`. -/
def OldRVRowSoundness {Input Output : Type} (family : PooledFamily) (before : Input → RV.State)
    (instruction : Input → RV.Instr) (words : Input → Output → (Nat → ZMod babyBearModulus) → Prop)
    (assumptions : PooledTrace babyBearModulus → RV.State → List Cell → List RVPooledProgramEntry → Prop)
    (conclusion : Input → Output → Prop) : Prop :=
  ∀ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry),
    assumptions trace initial cells program →
    ∀ input output w, (rvRowModel family before instruction words trace initial cells program).relation input output w →
      conclusion input output

/-- The assumptions of a per-row RV claim can be met (lean-strategies 3.3): some public setup meeting `assumptions`
    has a row of `family` that the model relates to some input and output. -/
def OldRVRowSatisfiable {Input Output : Type} (family : PooledFamily) (before : Input → RV.State)
    (instruction : Input → RV.Instr) (words : Input → Output → (Nat → ZMod babyBearModulus) → Prop)
    (assumptions : PooledTrace babyBearModulus → RV.State → List Cell → List RVPooledProgramEntry → Prop) : Prop :=
  ∃ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell)
    (program : List RVPooledProgramEntry) (input : Input) (output : Output) (w : Nat → ZMod babyBearModulus),
    assumptions trace initial cells program ∧
      (rvRowModel family before instruction words trace initial cells program).relation input output w

/-- A per-row RV claim: `OldRVRowSoundness`, and its assumptions can be met (`OldRVRowSatisfiable`). -/
def OldRVRowClaim {Input Output : Type} (family : PooledFamily) (before : Input → RV.State)
    (instruction : Input → RV.Instr) (words : Input → Output → (Nat → ZMod babyBearModulus) → Prop)
    (assumptions : PooledTrace babyBearModulus → RV.State → List Cell → List RVPooledProgramEntry → Prop)
    (conclusion : Input → Output → Prop) : Prop :=
  OldRVRowSoundness family before instruction words assumptions conclusion ∧
    OldRVRowSatisfiable family before instruction words assumptions

end Checks.Restatements

namespace Airbender.AddSub.Restatement

/-- The source row contract before its soundness and non-vacuity statements are separated. -/
def OldRVSoundnessClaim : Prop :=
  Checks.Restatements.OldRVRowClaim .addSub RVInput.before rvInstruction RVWordMapping RVInterfaceAssumptions fun input output =>
    ∃ s', RV.step input.before = some s' ∧
      RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

/-- The two reviewed statements preserve the complete source contract. -/
theorem claims_restatement : (RVSoundnessClaim ∧ RVSatisfiableClaim) ↔ OldRVSoundnessClaim := Iff.rfl

/-- Soundness preserves the source contract because its non-vacuity claim is proved separately. -/
theorem soundness_restatement : RVSoundnessClaim ↔ OldRVSoundnessClaim :=
  ⟨fun h => claims_restatement.mp ⟨h, rv_satisfiable⟩, fun h => (claims_restatement.mpr h).1⟩

/-- The separate non-vacuity statement preserves the source witness condition. -/
theorem satisfiable_restatement : RVSatisfiableClaim ↔
    Checks.Restatements.OldRVRowSatisfiable .addSub RVInput.before rvInstruction RVWordMapping RVInterfaceAssumptions := Iff.rfl

end Airbender.AddSub.Restatement

namespace Airbender.MulDiv.Restatement

/-- The source row contract before its soundness and non-vacuity statements are separated. -/
def OldRVSoundnessClaim : Prop :=
  Checks.Restatements.OldRVRowClaim .mulDiv RVInput.before rvInstruction RVWordMapping Trace.RVPooledHistoryInputs fun input output =>
    ∃ s', RV.step input.before = some s' ∧
      RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

/-- The two reviewed statements preserve the complete source contract. -/
theorem claims_restatement : (RVSoundnessClaim ∧ RVSatisfiableClaim) ↔ OldRVSoundnessClaim := Iff.rfl

/-- Soundness preserves the source contract because its non-vacuity claim is proved separately. -/
theorem soundness_restatement : RVSoundnessClaim ↔ OldRVSoundnessClaim :=
  ⟨fun h => claims_restatement.mp ⟨h, rv_satisfiable⟩, fun h => (claims_restatement.mpr h).1⟩

/-- The separate non-vacuity statement preserves the source witness condition. -/
theorem satisfiable_restatement : RVSatisfiableClaim ↔
    Checks.Restatements.OldRVRowSatisfiable .mulDiv RVInput.before rvInstruction RVWordMapping Trace.RVPooledHistoryInputs := Iff.rfl

end Airbender.MulDiv.Restatement

namespace Airbender.ShiftBinop.Restatement

/-- The source row contract before its soundness and non-vacuity statements are separated. -/
def OldRVSoundnessClaim : Prop :=
  Checks.Restatements.OldRVRowClaim .shiftBinop RVInput.before rvInstruction RVWordMapping Trace.RVPooledHistoryInputs fun input output =>
    ∃ s', RV.step input.before = some s' ∧
      RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

/-- The two reviewed statements preserve the complete source contract. -/
theorem claims_restatement : (RVSoundnessClaim ∧ RVSatisfiableClaim) ↔ OldRVSoundnessClaim := Iff.rfl

/-- Soundness preserves the source contract because its non-vacuity claim is proved separately. -/
theorem soundness_restatement : RVSoundnessClaim ↔ OldRVSoundnessClaim :=
  ⟨fun h => claims_restatement.mp ⟨h, rv_satisfiable⟩, fun h => (claims_restatement.mpr h).1⟩

/-- The separate non-vacuity statement preserves the source witness condition. -/
theorem satisfiable_restatement : RVSatisfiableClaim ↔
    Checks.Restatements.OldRVRowSatisfiable .shiftBinop RVInput.before rvInstruction RVWordMapping Trace.RVPooledHistoryInputs := Iff.rfl

end Airbender.ShiftBinop.Restatement

namespace Airbender.SubwordMemory.Restatement

/-- The source row contract before its soundness and non-vacuity statements are separated. -/
def OldRVSoundnessClaim : Prop :=
  Checks.Restatements.OldRVRowClaim .subwordMemory RVInput.before rvInstruction RVWordMapping Trace.RVPooledHistoryInputs fun input output =>
    output.cell.toBitVec.toNat = (input.source.toBitVec + input.immediate.toBitVec).toNat / 4 * 4 ∧
    ∃ s', RV.step input.before = some s' ∧
      RV.Same s' (if input.store then
          (input.before.store output.cell.toBitVec output.data.toBitVec 4).setPC output.pc.toBitVec
        else (input.before.setReg input.rd output.data.toBitVec).setPC output.pc.toBitVec)

/-- The two reviewed statements preserve the complete source contract. -/
theorem claims_restatement : (RVSoundnessClaim ∧ RVSatisfiableClaim) ↔ OldRVSoundnessClaim := Iff.rfl

/-- Soundness preserves the source contract because its non-vacuity claim is proved separately. -/
theorem soundness_restatement : RVSoundnessClaim ↔ OldRVSoundnessClaim :=
  ⟨fun h => claims_restatement.mp ⟨h, rv_satisfiable⟩, fun h => (claims_restatement.mpr h).1⟩

/-- The separate non-vacuity statement preserves the source witness condition. -/
theorem satisfiable_restatement : RVSatisfiableClaim ↔
    Checks.Restatements.OldRVRowSatisfiable .subwordMemory RVInput.before rvInstruction RVWordMapping Trace.RVPooledHistoryInputs := Iff.rfl

end Airbender.SubwordMemory.Restatement

namespace Airbender.WordMemory.Restatement

/-- The source row contract before its soundness and non-vacuity statements are separated. -/
def OldRVSoundnessClaim : Prop :=
  Checks.Restatements.OldRVRowClaim .wordMemory RVInput.before rvInstruction RVWordMapping Trace.RVPooledHistoryInputs fun input output =>
    output.address.toBitVec = input.source.toBitVec + input.immediate.toBitVec ∧
    ∃ s', RV.step input.before = some s' ∧
      RV.Same s' (if input.store then
          (input.before.store output.address.toBitVec output.data.toBitVec 4).setPC output.pc.toBitVec
        else (input.before.setReg input.rd output.data.toBitVec).setPC output.pc.toBitVec)

/-- The two reviewed statements preserve the complete source contract. -/
theorem claims_restatement : (RVSoundnessClaim ∧ RVSatisfiableClaim) ↔ OldRVSoundnessClaim := Iff.rfl

/-- Soundness preserves the source contract because its non-vacuity claim is proved separately. -/
theorem soundness_restatement : RVSoundnessClaim ↔ OldRVSoundnessClaim :=
  ⟨fun h => claims_restatement.mp ⟨h, rv_satisfiable⟩, fun h => (claims_restatement.mpr h).1⟩

/-- The separate non-vacuity statement preserves the source witness condition. -/
theorem satisfiable_restatement : RVSatisfiableClaim ↔
    Checks.Restatements.OldRVRowSatisfiable .wordMemory RVInput.before rvInstruction RVWordMapping Trace.RVPooledHistoryInputs := Iff.rfl

end Airbender.WordMemory.Restatement

namespace Airbender.JumpBranchSlt.Comparison.Restatement

/-- The source row contract before its soundness and non-vacuity statements are separated. -/
def OldRVSoundnessClaim : Prop :=
  Checks.Restatements.OldRVRowClaim .jumpBranchSlt RVInput.before rvInstruction RVWordMapping RVTraceInputs fun input output =>
    ∃ s', RV.step input.before = some s' ∧
      RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

/-- The two reviewed statements preserve the complete source contract. -/
theorem claims_restatement : (RVSoundnessClaim ∧ RVSatisfiableClaim) ↔ OldRVSoundnessClaim := Iff.rfl

/-- Soundness preserves the source contract because its non-vacuity claim is proved separately. -/
theorem soundness_restatement : RVSoundnessClaim ↔ OldRVSoundnessClaim :=
  ⟨fun h => claims_restatement.mp ⟨h, rv_satisfiable⟩, fun h => (claims_restatement.mpr h).1⟩

/-- The separate non-vacuity statement preserves the source witness condition. -/
theorem satisfiable_restatement : RVSatisfiableClaim ↔
    Checks.Restatements.OldRVRowSatisfiable .jumpBranchSlt RVInput.before rvInstruction RVWordMapping RVTraceInputs := Iff.rfl

end Airbender.JumpBranchSlt.Comparison.Restatement

namespace Airbender.JumpBranchSlt.Branch.Restatement

/-- The source row contract before its soundness and non-vacuity statements are separated. -/
def OldRVSoundnessClaim : Prop :=
  Checks.Restatements.OldRVRowClaim .jumpBranchSlt RVInput.before rvInstruction RVWordMapping RVTraceInputs fun input output =>
    ∃ s', RV.step input.before = some s' ∧ RV.Same s' (input.before.setPC output.pc.toBitVec)

/-- The two reviewed statements preserve the complete source contract. -/
theorem claims_restatement : (RVSoundnessClaim ∧ RVSatisfiableClaim) ↔ OldRVSoundnessClaim := Iff.rfl

/-- Soundness preserves the source contract because its non-vacuity claim is proved separately. -/
theorem soundness_restatement : RVSoundnessClaim ↔ OldRVSoundnessClaim :=
  ⟨fun h => claims_restatement.mp ⟨h, rv_satisfiable⟩, fun h => (claims_restatement.mpr h).1⟩

/-- The separate non-vacuity statement preserves the source witness condition. -/
theorem satisfiable_restatement : RVSatisfiableClaim ↔
    Checks.Restatements.OldRVRowSatisfiable .jumpBranchSlt RVInput.before rvInstruction RVWordMapping RVTraceInputs := Iff.rfl

end Airbender.JumpBranchSlt.Branch.Restatement

namespace Airbender.JumpBranchSlt.Jump.Restatement

/-- The source row contract before its soundness and non-vacuity statements are separated. -/
def OldRVSoundnessClaim : Prop :=
  Checks.Restatements.OldRVRowClaim .jumpBranchSlt RVInput.before rvInstruction RVWordMapping RVTraceInputs fun input output =>
    ∃ s', RV.step input.before = some s' ∧
      RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

/-- The two reviewed statements preserve the complete source contract. -/
theorem claims_restatement : (RVSoundnessClaim ∧ RVSatisfiableClaim) ↔ OldRVSoundnessClaim := Iff.rfl

/-- Soundness preserves the source contract because its non-vacuity claim is proved separately. -/
theorem soundness_restatement : RVSoundnessClaim ↔ OldRVSoundnessClaim :=
  ⟨fun h => claims_restatement.mp ⟨h, rv_satisfiable⟩, fun h => (claims_restatement.mpr h).1⟩

/-- The separate non-vacuity statement preserves the source witness condition. -/
theorem satisfiable_restatement : RVSatisfiableClaim ↔
    Checks.Restatements.OldRVRowSatisfiable .jumpBranchSlt RVInput.before rvInstruction RVWordMapping RVTraceInputs := Iff.rfl

end Airbender.JumpBranchSlt.Jump.Restatement

namespace Checks.Restatements
open Airbender Airbender.Trace

/-- The shape of the whole-trace claims over a public program: every accepted trace whose public boundary meets
    `inputs` and whose rows are `decoded` against the program is a run of our spec (`RVRealizes`). -/
def OldRVTraceSoundness {Kind : Type} [CircuitLayout Kind] {Program : Type}
    (inputs : Data babyBearModulus Kind → RV.State → List Cell → Program → Prop)
    (decoded : Data babyBearModulus Kind → Program → Prop) : Prop :=
  ∀ {trace : Data babyBearModulus Kind} {initial : RV.State} {cells : List Cell} {program : Program},
    inputs trace initial cells program → Accepted trace → decoded trace program → RVRealizes trace initial cells

/-- The assumptions of an `OldRVTraceSoundness inputs decoded` claim can be met, by a trace with a row. -/
def OldRVTraceSatisfiable {Kind : Type} [CircuitLayout Kind] {Program : Type}
    (inputs : Data babyBearModulus Kind → RV.State → List Cell → Program → Prop)
    (decoded : Data babyBearModulus Kind → Program → Prop) : Prop :=
  ∃ (trace : Data babyBearModulus Kind) (initial : RV.State) (cells : List Cell) (program : Program),
    inputs trace initial cells program ∧ Accepted trace ∧ decoded trace program ∧ trace.rows ≠ []

end Checks.Restatements

namespace Airbender.Trace.Restatement

/-- The source trace statement. -/
def OldRVAirbenderSoundnessClaim : Prop := Checks.Restatements.OldRVTraceSoundness RVExecutionBoundary RVDecoded

/-- The explicit trace statement preserves its source contract. -/
theorem RVAirbenderSoundnessClaim_restatement : RVAirbenderSoundnessClaim ↔ OldRVAirbenderSoundnessClaim := Iff.rfl

end Airbender.Trace.Restatement

namespace Airbender.Trace.Restatement

/-- The source trace statement. -/
def OldRVAirbenderSoundnessSatisfiableClaim : Prop := Checks.Restatements.OldRVTraceSatisfiable RVExecutionBoundary RVDecoded

/-- The explicit trace statement preserves its source contract. -/
theorem RVAirbenderSoundnessSatisfiableClaim_restatement : RVAirbenderSoundnessSatisfiableClaim ↔ OldRVAirbenderSoundnessSatisfiableClaim := Iff.rfl

end Airbender.Trace.Restatement

namespace Airbender.JumpBranchSlt.Restatement

/-- The source trace statement. -/
def OldRVTraceSoundnessClaim : Prop := Checks.Restatements.OldRVTraceSoundness RVExecutionInputs RVDecoded

/-- The explicit trace statement preserves its source contract. -/
theorem RVTraceSoundnessClaim_restatement : RVTraceSoundnessClaim ↔ OldRVTraceSoundnessClaim := Iff.rfl

end Airbender.JumpBranchSlt.Restatement

namespace Airbender.JumpBranchSlt.Restatement

/-- The source trace statement. -/
def OldRVTraceSoundnessSatisfiableClaim : Prop := Checks.Restatements.OldRVTraceSatisfiable RVExecutionInputs RVDecoded

/-- The explicit trace statement preserves its source contract. -/
theorem RVTraceSoundnessSatisfiableClaim_restatement : RVTraceSoundnessSatisfiableClaim ↔ OldRVTraceSoundnessSatisfiableClaim := Iff.rfl

end Airbender.JumpBranchSlt.Restatement

namespace Airbender.MulDiv.Restatement

/-- The source trace statement. -/
def OldRVTraceSoundnessClaim : Prop := Checks.Restatements.OldRVTraceSoundness RVExecutionInputs RVDecoded

/-- The explicit trace statement preserves its source contract. -/
theorem RVTraceSoundnessClaim_restatement : RVTraceSoundnessClaim ↔ OldRVTraceSoundnessClaim := Iff.rfl

end Airbender.MulDiv.Restatement

namespace Airbender.MulDiv.Restatement

/-- The source trace statement. -/
def OldRVTraceSoundnessSatisfiableClaim : Prop := Checks.Restatements.OldRVTraceSatisfiable RVExecutionInputs RVDecoded

/-- The explicit trace statement preserves its source contract. -/
theorem RVTraceSoundnessSatisfiableClaim_restatement : RVTraceSoundnessSatisfiableClaim ↔ OldRVTraceSoundnessSatisfiableClaim := Iff.rfl

end Airbender.MulDiv.Restatement

namespace Airbender.ShiftBinop.Restatement

/-- The source trace statement. -/
def OldRVTraceSoundnessClaim : Prop := Checks.Restatements.OldRVTraceSoundness RVExecutionInputs RVDecoded

/-- The explicit trace statement preserves its source contract. -/
theorem RVTraceSoundnessClaim_restatement : RVTraceSoundnessClaim ↔ OldRVTraceSoundnessClaim := Iff.rfl

end Airbender.ShiftBinop.Restatement

namespace Airbender.ShiftBinop.Restatement

/-- The source trace statement. -/
def OldRVTraceSoundnessSatisfiableClaim : Prop := Checks.Restatements.OldRVTraceSatisfiable RVExecutionInputs RVDecoded

/-- The explicit trace statement preserves its source contract. -/
theorem RVTraceSoundnessSatisfiableClaim_restatement : RVTraceSoundnessSatisfiableClaim ↔ OldRVTraceSoundnessSatisfiableClaim := Iff.rfl

end Airbender.ShiftBinop.Restatement

namespace Airbender.SubwordMemory.Restatement

/-- The source trace statement. -/
def OldRVRamTraceSoundnessClaim : Prop := Checks.Restatements.OldRVTraceSoundness RVRAMInputs RVDecoded

/-- The explicit trace statement preserves its source contract. -/
theorem RVRamTraceSoundnessClaim_restatement : RVRamTraceSoundnessClaim ↔ OldRVRamTraceSoundnessClaim := Iff.rfl

end Airbender.SubwordMemory.Restatement

namespace Airbender.SubwordMemory.Restatement

/-- The source trace statement. -/
def OldRVRamTraceSoundnessSatisfiableClaim : Prop := Checks.Restatements.OldRVTraceSatisfiable RVRAMInputs RVDecoded

/-- The explicit trace statement preserves its source contract. -/
theorem RVRamTraceSoundnessSatisfiableClaim_restatement : RVRamTraceSoundnessSatisfiableClaim ↔ OldRVRamTraceSoundnessSatisfiableClaim := Iff.rfl

end Airbender.SubwordMemory.Restatement

namespace Airbender.Bigint.Memory.Restatement

/-- The source property statement. -/
def OldRVAddressesSoundnessClaim : Prop :=
  ∀ (data : Delegation.MemoryData babyBearModulus) (before : RV.State) (cells : List Trace.Cell),
    (circuitModel data).SoundnessUnder (RVInterfaceAssumptions data before cells) Addresses.spec

/-- The explicit relation preserves the source property. -/
theorem property_restatement : RVAddressesSoundnessClaim ↔ OldRVAddressesSoundnessClaim := Iff.rfl

end Airbender.Bigint.Memory.Restatement

namespace Airbender.Blake2G.Restatement

/-- The source property statement. -/
def OldSoundnessClaim : Prop :=
  ∀ (control : Fin 512 → Vector Nat 7),
    (circuitModel (p := babyBearModulus) control).SoundnessUnder (InterfaceAssumptions (p := babyBearModulus)) spec

/-- The explicit relation preserves the source property. -/
theorem property_restatement : SoundnessClaim ↔ OldSoundnessClaim := Iff.rfl

end Airbender.Blake2G.Restatement

namespace Airbender.InitsTeardowns.Restatement
open Trace

/-- The source initialization contract. -/
def OldStandaloneClaim : Prop :=
  Claims importedLayout ∧
    ∀ address : BitVec 32, (Cell.ram address).Aligned →
      Cell.ram address ∈ windowCells importedLayout (List.range maxTopBit)

/-- The explicit properties and witness condition preserve the source contract. -/
theorem standalone_claims_restatement : (StandaloneClaim ∧ StandaloneSatisfiableClaim) ↔ OldStandaloneClaim := by
  constructor
  · rintro ⟨⟨init, boot, teardown, coverage⟩, ⟨topBits, rfl, checked⟩⟩
    exact ⟨⟨init, boot, teardown, checked⟩, coverage⟩
  · rintro ⟨properties, coverage⟩
    exact ⟨⟨properties.init, properties.bootImage, properties.teardown, coverage⟩,
      ⟨_, rfl, properties.checkable⟩⟩

/-- The separate witness proof preserves the source soundness contract. -/
theorem standalone_restatement : StandaloneClaim ↔ OldStandaloneClaim :=
  ⟨fun h => standalone_claims_restatement.mp ⟨h, standalone_satisfiable⟩,
    fun h => (standalone_claims_restatement.mpr h).1⟩

end Airbender.InitsTeardowns.Restatement

namespace Airbender.InitsTeardowns.Restatement
open Trace

/-- The source initialization contract. -/
def OldUnifiedClaim : Prop :=
  Claims unifiedLayout ∧
    ∀ address : BitVec 32, (Cell.ram address).Aligned → address.toNat < 2 ^ 31 →
      Cell.ram address ∈ windowCells unifiedLayout (List.range maxTopBit)

/-- The explicit properties and witness condition preserve the source contract. -/
theorem unified_claims_restatement : (UnifiedClaim ∧ UnifiedSatisfiableClaim) ↔ OldUnifiedClaim := by
  constructor
  · rintro ⟨⟨init, boot, teardown, coverage⟩, ⟨topBits, rfl, checked⟩⟩
    exact ⟨⟨init, boot, teardown, checked⟩, coverage⟩
  · rintro ⟨properties, coverage⟩
    exact ⟨⟨properties.init, properties.bootImage, properties.teardown, coverage⟩,
      ⟨_, rfl, properties.checkable⟩⟩

/-- The separate witness proof preserves the source soundness contract. -/
theorem unified_restatement : UnifiedClaim ↔ OldUnifiedClaim :=
  ⟨fun h => unified_claims_restatement.mp ⟨h, unified_satisfiable⟩,
    fun h => (unified_claims_restatement.mpr h).1⟩

end Airbender.InitsTeardowns.Restatement
